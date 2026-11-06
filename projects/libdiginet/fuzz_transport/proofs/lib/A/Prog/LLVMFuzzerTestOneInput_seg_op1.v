(* LLVMFuzzerTestOneInput_seg_op1: segment OP1 of the image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput
   (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v lc_op1_stmt, +0x5e8 .. +0x1114, from the cut ARM1 to the cut BAR1):
   op 1, the inlined op_frame: the checked byte loads of sel, send, ack, retry and w at the cursor, g_last_counter
   when sel & 0x80, len = min (w mod 1485, bytes left), the checked 8-byte loads of op_frame.DST / SRC and the checked
   byte load of op_frame.CMD. No call, no byte written.

   The run is lib/A/Prog/LLVMFuzzerTestOneInput_seg_op1_run.v op1_run_post (a footprint run of lib/Lib/ExecF.v,
   carried into SRr by DgnTransportCgRun.v decode_run). Here the cut state's facts become the run's premises:
     the input bytes and the shadow byte of each (the caller's block, trans_src_ok_rd; check_state_desk_seg_bridge.v
       csd_bytes_of_garr, csd_shadow_any);
     the spill slots at sp1 + 48 (g_last_counter's page), + 96 (0x610f) and + 136 (0xffff) (lc_spills, op1_word_read);
     g_last_counter's four bytes (lc_tw at TMAP_A's row, TWorldG.v tw_bytes_at);
     op_frame.DST / SRC / CMD as the image holds them (K1, lc_rom_view_stmt, taken as an argument: its sub-row is
       AW72ag) and their shadow bytes (transport_cells: the zero-shadow rows of DST / SRC, CMD's partial granule 7);
     the footprint (RNG_W W': every byte the run reads is visible).
   After the run the memory is the cut's and the model only materializes pages, so lc_lcore carries over (the journal
   by W_journalG.v ajournal_gx_materialize) and the call's arguments are lc_frame_vals' fields (op1_frame_vals). *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YA0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG TransportShape.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCgRun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_desk_seg_kit check_state_desk_seg_bridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_seg_op1_run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require LLVMFuzzerTestOneInput_op1.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module POP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.LLVMFuzzerTestOneInput_op1.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the facts the run reads, from the cut state ---- *)

(* An 8-byte word of the view (a spill slot), as the bytes the run's load reads, and those bytes visible. *)
Lemma op1_word_read : forall (W : world tfibsegs) (m : word -> option byte) a v,
  rdword (aview tfibsegs (w_H W) m) a = Some v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 8 = Some (le8 (Z_to_bv 64 v)) /\
  (forall i, 0 <= i < 8 -> w_H W (Z_to_bv 64 (a + i)) = false).
Proof.
  intros W m a v Hw H0 H1.
  pose proof (YCbq.val_mem_of_rdword tfibsegs (w_H W) m a v Hw) as HV.
  assert (VIS : forall i, 0 <= i < 8 -> w_H W (Z_to_bv 64 (a + i)) = false).
  { intros i Hi. specialize (HV (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HV by lia.
    apply (decode_aview_vis W m (a + i) (bv_unsigned (Z_to_bv 8 (le_byte v 8 (Z.to_nat i))))).
    unfold aview. rewrite HV. reflexivity. }
  split; [|exact VIS].
  change (Z_to_bv 64 a) with (wa a). apply csd_rdall; [|apply length_le8].
  split; [lia|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi.
  rewrite (csd_mrd_of_mbyte W m (a + Z.of_nat i) (VIS (Z.of_nat i) ltac:(lia))).
  rewrite (HV i Hi).
  pose proof (decode_le8_byte v i Hi) as E.
  destruct (nth_error (le8 (wa v)) i) as [b|] eqn:Eb; [|discriminate E].
  change (le8 (Z_to_bv 64 v)) with (le8 (wa v)). rewrite Eb. f_equal.
  cbn [option_map] in E. injection E as E. apply bv_eq. rewrite E, Z_to_bv_unsigned.
  unfold le_byte. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

(* Bytes of the read-only image the walk reads (TRANS_RO_RD), decided against the image. *)
Definition op1_rom_ok (q : Z) (bs : list byte) : bool :=
  forallb (fun j => match PropExec.seg_rom rsegs (wa (q + Z.of_nat j)) with
                    | Some b => bv_unsigned b =? bv_unsigned (nth j bs (Z_to_bv 8 0))
                    | None => false
                    end) (seq 0 (length bs)).

Lemma op1_rom_read : forall (W : world tfibsegs) m q bs (n : nat),
  trans_rom_view_rd W m -> (forall a, q <= a < q + Z.of_nat (length bs) -> trans_in_ro_rd a) ->
  op1_rom_ok q bs = true -> length bs = n -> 0 <= q -> q + Z.of_nat n <= 2 ^ 64 ->
  ov_read_bytes rsegs m (Z_to_bv 64 q) n = Some bs.
Proof.
  intros W m q bs n HROM Hin Hok Hl H0 H1.
  change (Z_to_bv 64 q) with (wa q). apply csd_rdall; [|exact Hl].
  split; [lia|]. split; [lia|].
  intros j Hj. unfold op1_rom_ok in Hok. rewrite forallb_forall in Hok.
  specialize (Hok j (proj2 (in_seq _ _ _) (conj (Nat.le_0_l j) Hj))).
  rewrite (proj2 (csd_ro_byte W m (q + Z.of_nat j) HROM (Hin (q + Z.of_nat j) ltac:(lia)))).
  destruct (PropExec.seg_rom rsegs (wa (q + Z.of_nat j))) as [b|]; [|discriminate Hok].
  apply Z.eqb_eq in Hok. rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hj). f_equal. apply bv_eq. exact Hok.
Qed.

(* A one-byte constant cell of the record (a shadow byte the runtime fixes), read at an AR state. *)
Lemma op1_z1_mrd : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 ->
  w_H W (Z_to_bv 64 a) = false /\ mrd rsegs mem (wa a) = Some (Z_to_bv 8 v).
Proof.
  intros rc B ly S W mem md a v [M _] Hin Hv.
  assert (HK : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) by (eapply am_const; exact M).
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as Hc.
  unfold cell_holds, z1, c1 in Hc. cbn [aeval c_at c_w c_val] in Hc.
  specialize (Hc 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hc. rewrite Z.add_0_r in Hc.
  destruct (decode_aview_some W mem a _ Hc) as (Hvis & b & Hb & Eb).
  split; [exact Hvis|]. rewrite Hb. f_equal. apply bv_eq. rewrite Eb, Z_to_bv_unsigned.
  unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8). rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* op_frame's values (lc_frame_vals) are the run's, from the cursor after the op byte. *)
Lemma op1_frame_vals : forall (D Bw : list byte) (c : TOP.fuzz_in),
  0 <= TOP.fi_n c -> TOP.fi_n c <> 0 ->
  lc_frame_vals D Bw (lc_oc D c) =
  mkLfv (og (TOP.fi_off c) (TOP.fi_n c) D 0) (r_send (TOP.fi_off c) (TOP.fi_n c) D)
        (r_ack (TOP.fi_off c) (TOP.fi_n c) D Bw) (r_retry (TOP.fi_off c) (TOP.fi_n c) D)
        (TOP.fi_off c + 1 + Z.min 8 (TOP.fi_n c - 1)) (r_len (TOP.fi_off c) (TOP.fi_n c) D)
        (TOP.FuzzIn (TOP.fi_off c + 1 + Z.min 8 (TOP.fi_n c - 1) + r_len (TOP.fi_off c) (TOP.fi_n c) D)
                    (r_nr (TOP.fi_n c) - r_len (TOP.fi_off c) (TOP.fi_n c) D)).
Proof.
  intros D Bw c Hn0 Hn.
  set (c1 := TOP.FuzzIn (TOP.fi_off c + 1) (TOP.fi_n c - 1)).
  assert (E1 : lc_oc D c = c1).
  { unfold lc_oc, TOP.fuzz_u8_m. rewrite (proj2 (Z.eqb_neq _ 0) Hn). reflexivity. }
  assert (Hc1 : 0 <= TOP.fi_n c1) by (unfold c1; cbn; lia).
  pose proof (og_range (TOP.fi_off c) (TOP.fi_n c) D) as RG.
  assert (G : forall j, POP.op1_g D c1 j = og (TOP.fi_off c) (TOP.fi_n c) D j) by reflexivity.
  assert (E0 : TOP.fuzz_u8_m D c1 = (POP.op1_adv c1 1, POP.op1_g D c1 0)).
  { pose proof (POP.op1_u8 D c1 0 ltac:(lia) Hc1) as E. rewrite POP.op1_adv0 in E by exact Hc1. exact E. }
  assert (E2 : TOP.fuzz_u16_m D (POP.op1_adv c1 1) =
               (POP.op1_adv c1 3, Z.lor (POP.op1_g D c1 1) (Z.shiftl (POP.op1_g D c1 2) 8) mod 2 ^ 16))
    by exact (POP.op1_u16 D c1 1 ltac:(lia) Hc1).
  assert (E3 : TOP.fuzz_u16_m D (POP.op1_adv c1 3) =
               (POP.op1_adv c1 5, Z.lor (POP.op1_g D c1 3) (Z.shiftl (POP.op1_g D c1 4) 8) mod 2 ^ 16))
    by exact (POP.op1_u16 D c1 3 ltac:(lia) Hc1).
  assert (E4 : TOP.fuzz_u8_m D (POP.op1_adv c1 5) = (POP.op1_adv c1 6, POP.op1_g D c1 5))
    by exact (POP.op1_u8 D c1 5 ltac:(lia) Hc1).
  assert (E5 : TOP.fuzz_u16_m D (POP.op1_adv c1 6) =
               (POP.op1_adv c1 8, Z.lor (POP.op1_g D c1 6) (Z.shiftl (POP.op1_g D c1 7) 8) mod 2 ^ 16))
    by exact (POP.op1_u16 D c1 6 ltac:(lia) Hc1).
  rewrite E1. unfold lc_frame_vals.
  rewrite E0; cbv beta iota zeta. rewrite E2; cbv beta iota zeta. rewrite E3; cbv beta iota zeta.
  rewrite E4; cbv beta iota zeta. rewrite E5; cbv beta iota zeta.
  rewrite !G.
  pose proof (RG 1). pose proof (RG 2). pose proof (RG 3). pose proof (RG 4). pose proof (RG 6). pose proof (RG 7).
  rewrite !(Z.mod_small (Z.lor _ (Z.shiftl _ 8)) (2 ^ 16)) by (rewrite Bytes.lor_shiftl8_add by lia; lia).
  unfold TOP.fuzz_take_m. cbn [TOP.fi_off TOP.fi_n POP.op1_adv c1].
  change (TC.SPEC_MAX_BODY + 1) with 1485.
  unfold r_send, r_ack, r_retry, r_len, r_nr, r_w.
  change 0x80 with 128.
  replace (Z.min 2 (TOP.fi_n c - 1)) with (Z.min 2 (TOP.fi_n c - 1)) by reflexivity.
  f_equal; try reflexivity;
    try (destruct (Z.ltb_spec (Z.lor (og (TOP.fi_off c) (TOP.fi_n c) D 6)
                                     (Z.shiftl (og (TOP.fi_off c) (TOP.fi_n c) D 7) 8) mod 1485)
                              (TOP.fi_n c - 1 - Z.min 8 (TOP.fi_n c - 1))); lia).
  destruct (Z.ltb_spec (Z.lor (og (TOP.fi_off c) (TOP.fi_n c) D 6) (Z.shiftl (og (TOP.fi_off c) (TOP.fi_n c) D 7) 8)
                          mod 1485) (TOP.fi_n c - 1 - Z.min 8 (TOP.fi_n c - 1))); f_equal; lia.
Qed.

Section seg1. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

Theorem lc_op1_ok (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) : @lc_op1_stmt rc B MT XL RLO RHI.
Proof.
  unfold lc_op1_stmt. intros HP cx op W' c' HB HARM.
  destruct HARM as (ly' & S' & regs' & mem' & md' & e & -> & Ho & HL & HTW & (C25 & C27) & (C24 & C23) & R20 & R22).
  pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & HME & R21).
  pose proof HOK as (HAG & Hops & (HcO & HcN & HcL) & Hn0 & Hkops).
  pose proof (K1 HP cx ly' S' W' regs' mem' md' e HB HC) as HROM.
  pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as GEO.
  destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HIN Hlive].
  pose proof HC as (HJ & Hfrs & HlyF & HPERM & R2 & R8 & R9 & R3 & R4 & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil
                    & HFpres & HFL & HINP).
  pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
  pose proof (lp_cells _ _ _ _ _ HP) as HCELLS.
  pose proof asan_consts as ((CA1 & CA2) & CK1 & CK2 & CK3 & CK4).
  set (D := l_pl cx) in *. set (p := l_p cx) in *. set (c := lo_c op) in *. set (Bw := lo_B op) in *.
  set (O := TOP.fi_off c) in *. set (N := TOP.fi_n c) in *.
  assert (EOC : lc_oc D c = TOP.FuzzIn (O + 1) (N - 1))
    by (unfold lc_oc, TOP.fuzz_u8_m; rewrite (proj2 (Z.eqb_neq (TOP.fi_n c) 0) Hn0); reflexivity).
  rewrite EOC in C24, C23. cbn [TOP.fi_off TOP.fi_n] in C24, C23.
  destruct Hn as (Hn26 & HnL).
  assert (HnD : l_n cx = O + N) by lia.
  assert (HN1 : 1 <= N) by lia.
  assert (HN26 : N < 2 ^ 26) by lia.
  (* ---- the input: a readable range of the caller's block, its bytes and shadow bytes ---- *)
  assert (RDP : decode_rd_ok W' mem' p (l_n cx)).
  { eapply trans_src_ok_rd; [exact LAWS | exact HAR | left; exists p, (l_n cx); split; [exact (HIN ltac:(lia)) | lia]
      | lia]. }
  pose proof RDP as (_ & _ & _ & HAM & Hp0 & Hp63).
  assert (HPN : p + O + N < 2 ^ 62) by (unfold amem_range in HAM; lia).
  assert (BD : bytes_at rsegs mem' p D).
  { apply (csd_bytes_of_garr W' mem' p D); [lia | lia | | exact (proj1 HINP)].
    intros a Ha. apply (csd_vis_rd W' mem' p (l_n cx) a RDP). lia. }
  assert (HRB : forall k, 0 <= k < N ->
    ov_read_bytes rsegs mem' (Z_to_bv 64 (p + O + k)) 1 = Some [nth (Z.to_nat (O + k)) D (Z_to_bv 8 0)]).
  { intros k Hk. apply (csd_rd1 mem' p D (Z.to_nat (O + k)) (p + O + k) BD); lia. }
  assert (HSH : forall k, 0 <= k < N -> exists sk : byte,
    mrd rsegs mem' (wa ((p + O + k) / 8 + 2147450880)) = Some sk /\
    (bv_signed sk = 0 \/ (p + O + k) mod 8 < bv_signed sk)).
  { intros k Hk. destruct (csd_shadow_any W' mem' p (l_n cx) (p + O + k) RDP ltac:(lia)) as (_ & sk & Hsk & Ok).
    exists sk. split; [exact Hsk | exact Ok]. }
  assert (HRD : forall k, 0 <= k < N -> rng (LCK.RNG_W (world segs) (@w_H segs) W') (p + O + k) 1).
  { intros k Hk. apply decode_rng; [lia | lia |]. intros b Hb. apply (csd_vis_rd W' mem' p (l_n cx) b RDP). lia. }
  assert (HRS : forall k, 0 <= k < N ->
    rng (LCK.RNG_W (world segs) (@w_H segs) W') ((p + O + k) / 8 + 2147450880) 1).
  { intros k Hk. pose proof (Z.div_pos (p + O + k) 8 ltac:(lia) ltac:(lia)) as D0.
    pose proof (Z.div_le_upper_bound (p + O + k) 8 (2 ^ 62) ltac:(lia) ltac:(lia)) as D1.
    apply decode_rng; [lia | lia |]. intros b Hb. replace b with ((p + O + k) / 8 + 2147450880) by lia.
    exact (proj1 (csd_shadow_any W' mem' p (l_n cx) (p + O + k) RDP ltac:(lia))). }
  (* ---- the spill slots at sp1 + 48, + 96, + 136 ---- *)
  unfold lc_spills in HSP. rewrite Forall_forall in HSP.
  destruct lf_spill_pages as (_ & _ & _ & E11 & _ & _).
  assert (SP48 : rdword (aview segs (w_H W') mem') (lc_sp1 cx + 48) = Some 0x5df568).
  { rewrite <- E11. apply (HSP (48, transport_hi 11)).
    unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app In].
    repeat (first [left; reflexivity | right]). }
  assert (SP96 : rdword (aview segs (w_H W') mem') (lc_sp1 cx + 96) = Some 0x610f).
  { apply (HSP (96, 0x610f)).
    unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app In].
    repeat (first [left; reflexivity | right]). }
  assert (SP136 : rdword (aview segs (w_H W') mem') (lc_sp1 cx + 136) = Some 0xffff).
  { apply (HSP (136, 0xffff)).
    unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app In].
    repeat (first [left; reflexivity | right]). }
  unfold LF_FRAME in Hsp1.
  assert (U1 : bv_unsigned (w64 (lc_sp1 cx)) = lc_sp1 cx) by (apply unsigned_lit; unfold lc_sp0 in *; lia).
  destruct (op1_word_read W' mem' (lc_sp1 cx + 48) 0x5df568 SP48 ltac:(lia) ltac:(unfold lc_sp0 in *; lia))
    as (M48' & V48).
  destruct (op1_word_read W' mem' (lc_sp1 cx + 96) 0x610f SP96 ltac:(lia) ltac:(unfold lc_sp0 in *; lia))
    as (M96' & V96).
  destruct (op1_word_read W' mem' (lc_sp1 cx + 136) 0xffff SP136 ltac:(lia) ltac:(unfold lc_sp0 in *; lia))
    as (M136' & V136).
  assert (M48 : ov_read_bytes rsegs mem' (Z_to_bv 64 (bv_unsigned (w64 (lc_sp1 cx)) + 48)) 8 =
                Some (le8 (Z_to_bv 64 0x5df568))) by (rewrite U1; exact M48').
  assert (M96 : ov_read_bytes rsegs mem' (Z_to_bv 64 (bv_unsigned (w64 (lc_sp1 cx)) + 96)) 8 =
                Some (le8 (Z_to_bv 64 0x610f))) by (rewrite U1; exact M96').
  assert (M136 : ov_read_bytes rsegs mem' (Z_to_bv 64 (bv_unsigned (w64 (lc_sp1 cx)) + 136)) 8 =
                 Some (le8 (Z_to_bv 64 0xffff))) by (rewrite U1; exact M136').
  assert (R48 : rng (LCK.RNG_W (world segs) (@w_H segs) W') (bv_unsigned (w64 (lc_sp1 cx)) + 48) 8)
    by (rewrite U1; apply decode_rng; [lia | unfold lc_sp0 in *; lia | intros b Hb;
        replace b with (lc_sp1 cx + 48 + (b - (lc_sp1 cx + 48))) by lia; apply V48; lia]).
  assert (R96 : rng (LCK.RNG_W (world segs) (@w_H segs) W') (bv_unsigned (w64 (lc_sp1 cx)) + 96) 8)
    by (rewrite U1; apply decode_rng; [lia | unfold lc_sp0 in *; lia | intros b Hb;
        replace b with (lc_sp1 cx + 96 + (b - (lc_sp1 cx + 96))) by lia; apply V96; lia]).
  assert (R136 : rng (LCK.RNG_W (world segs) (@w_H segs) W') (bv_unsigned (w64 (lc_sp1 cx)) + 136) 8)
    by (rewrite U1; apply decode_rng; [lia | unfold lc_sp0 in *; lia | intros b Hb;
        replace b with (lc_sp1 cx + 136 + (b - (lc_sp1 cx + 136))) by lia; apply V136; lia]).
  (* ---- g_last_counter (TMAP_A's row at 0x5df140) ---- *)
  pose proof (csd_tw_mrd W' mem' Bw HTW) as HTWm.
  pose proof (tw_bytes_at rsegs mem' TMAP_A Bw TW.OFF_g_last_counter TA_g_last_counter TW.SZ_g_last_counter 0 4
                TMAP_A_ok HTWm TMAP_A_g_last_counter ltac:(lia) ltac:(unfold TW.SZ_g_last_counter; lia)) as BLC.
  rewrite !Z.add_0_r in BLC.
  assert (MLC : ov_read_bytes rsegs mem' (Z_to_bv 64 6156608) 4 = Some (TW.sub Bw TW.OFF_g_last_counter 4)).
  { change (Z_to_bv 64 6156608) with (wa TA_g_last_counter). apply csd_rdall; [exact BLC|].
    apply csd_len_sub; [unfold TW.OFF_g_last_counter; lia | rewrite (proj1 HTW); unfold TW.OFF_g_last_counter, TW.W_LEN; lia]. }
  assert (RLC : rng (LCK.RNG_W (world segs) (@w_H segs) W') 6156608 4).
  { apply decode_rng; [lia | lia |]. intros b Hb. apply decode_vis_seg. apply trans_g_img.
    unfold W_journalG.inG. apply Exists_exists. exists (TA_g_last_counter, TW.SZ_g_last_counter).
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_last_counter) | unfold in_zr, TA_g_last_counter, TW.SZ_g_last_counter; cbn [fst snd]; lia]. }
  (* ---- op_frame.DST / SRC / CMD (image bytes, K1) and their shadow bytes (transport_cells) ---- *)
  assert (INRO : forall b n, In (b, n) TRANS_RO_RD -> forall a, b <= a < b + n -> trans_in_ro_rd a)
    by (intros b n Hin a Ha; apply Exists_exists; exists (b, n); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  assert (IDST : In (TRANS_DST, 32) TRANS_RO_RD)
    by (unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (ISRC : In (TRANS_SRC, 32) TRANS_RO_RD)
    by (unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (ICMD : In (TRANS_CMD, 7) TRANS_RO_RD)
    by (unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (MDST : forall i, 0 <= i < 4 -> ov_read_bytes rsegs mem' (Z_to_bv 64 (671264 + 8 * i)) 8 =
    Some (le8 (Z_to_bv 64 (nth (Z.to_nat i) [TRANS_HOST; TRANS_SPEC_BCAST; TRANS_OTHER; TRANS_HOST] 0)))).
  { intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct C as [C|[C|[C|C]]]; rewrite C;
      (apply (op1_rom_read W' mem'); [exact HROM | intros a Ha; apply (INRO _ _ IDST); rewrite length_le8 in Ha;
         unfold TRANS_DST; lia | vm_compute; reflexivity | reflexivity | lia | lia]). }
  assert (MSRC : forall i, 0 <= i < 4 -> ov_read_bytes rsegs mem' (Z_to_bv 64 (671200 + 8 * i)) 8 =
    Some (le8 (Z_to_bv 64 (nth (Z.to_nat i) [TRANS_DESK; TRANS_DESK2; TRANS_HOST; TRANS_NOTDD] 0)))).
  { intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct C as [C|[C|[C|C]]]; rewrite C;
      (apply (op1_rom_read W' mem'); [exact HROM | intros a Ha; apply (INRO _ _ ISRC); rewrite length_le8 in Ha;
         unfold TRANS_SRC; lia | vm_compute; reflexivity | reflexivity | lia | lia]). }
  assert (MCMD : forall i, 0 <= i < 7 -> ov_read_bytes rsegs mem' (Z_to_bv 64 (135424 + i)) 1 =
    Some [Z_to_bv 8 (nth (Z.to_nat i) TOP.op_frame_CMD 0)]).
  { intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; rewrite C;
      (apply (op1_rom_read W' mem'); [exact HROM | intros a Ha; apply (INRO _ _ ICMD); cbn [length Z.of_nat] in Ha;
         unfold TRANS_CMD; lia | vm_compute; reflexivity | reflexivity | lia | lia]). }
  destruct (HCELLS ly') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                            & _ & _ & _ & ZCMD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZSRC & ZDST & _ & _).
  assert (SH8 : forall i, (671264 + 8 * i) mod 8 = 0 /\ (671200 + 8 * i) mod 8 = 0)
    by (intros i; rewrite !(Z.mul_comm 8 i), !Z.mod_add by lia; split; reflexivity).
  assert (SDST : forall i, 0 <= i < 4 -> mrd rsegs mem' (wa ((671264 + 8 * i) / 8 + 2147450880)) = Some (Z_to_bv 8 0)).
  { intros i Hi. exact (proj2 (csd_zsh_byte B ly' S' W' mem' md' TRANS_DST (TRANS_DST + 32) (671264 + 8 * i)
                                 HAR ZDST (proj1 (SH8 i)) ltac:(unfold TRANS_DST; lia) ltac:(unfold TRANS_DST; lia))). }
  assert (SSRC : forall i, 0 <= i < 4 -> mrd rsegs mem' (wa ((671200 + 8 * i) / 8 + 2147450880)) = Some (Z_to_bv 8 0)).
  { intros i Hi. exact (proj2 (csd_zsh_byte B ly' S' W' mem' md' TRANS_SRC (TRANS_SRC + 32) (671200 + 8 * i)
                                 HAR ZSRC (proj2 (SH8 i)) ltac:(unfold TRANS_SRC; lia) ltac:(unfold TRANS_SRC; lia))). }
  pose proof (op1_z1_mrd B ly' S' W' mem' md' _ 7 HAR ZCMD ltac:(lia)) as (VCMD & MSCMD).
  assert (SCMD : forall i, 0 <= i < 7 -> mrd rsegs mem' (wa ((135424 + i) / 8 + 2147450880)) = Some (Z_to_bv 8 7)).
  { intros i Hi. replace ((135424 + i) / 8) with 16928 by (Z.div_mod_to_equations; lia). exact MSCMD. }
  assert (RDST : rng (LCK.RNG_W (world segs) (@w_H segs) W') 671264 32).
  { apply decode_rng; [lia | lia |]. intros b Hb.
    exact (proj1 (csd_ro_byte W' mem' b HROM (INRO _ _ IDST b ltac:(unfold TRANS_DST; lia)))). }
  assert (RSRC : rng (LCK.RNG_W (world segs) (@w_H segs) W') 671200 32).
  { apply decode_rng; [lia | lia |]. intros b Hb.
    exact (proj1 (csd_ro_byte W' mem' b HROM (INRO _ _ ISRC b ltac:(unfold TRANS_SRC; lia)))). }
  assert (RCMD : rng (LCK.RNG_W (world segs) (@w_H segs) W') 135424 7).
  { apply decode_rng; [lia | lia |]. intros b Hb.
    exact (proj1 (csd_ro_byte W' mem' b HROM (INRO _ _ ICMD b ltac:(unfold TRANS_CMD; lia)))). }
  assert (RSDST : forall i, 0 <= i < 4 -> rng (LCK.RNG_W (world segs) (@w_H segs) W') ((671264 + 8 * i) / 8 + 2147450880) 1).
  { intros i Hi. apply decode_rng; [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |]. intros b Hb.
    replace b with ((671264 + 8 * i) / 8 + 2147450880) by lia.
    exact (proj1 (csd_zsh_byte B ly' S' W' mem' md' TRANS_DST (TRANS_DST + 32) (671264 + 8 * i)
                    HAR ZDST (proj1 (SH8 i)) ltac:(unfold TRANS_DST; lia) ltac:(unfold TRANS_DST; lia))). }
  assert (RSSRC : forall i, 0 <= i < 4 -> rng (LCK.RNG_W (world segs) (@w_H segs) W') ((671200 + 8 * i) / 8 + 2147450880) 1).
  { intros i Hi. apply decode_rng; [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |]. intros b Hb.
    replace b with ((671200 + 8 * i) / 8 + 2147450880) by lia.
    exact (proj1 (csd_zsh_byte B ly' S' W' mem' md' TRANS_SRC (TRANS_SRC + 32) (671200 + 8 * i)
                    HAR ZSRC (proj2 (SH8 i)) ltac:(unfold TRANS_SRC; lia) ltac:(unfold TRANS_SRC; lia))). }
  assert (RSCMD : forall i, 0 <= i < 7 -> rng (LCK.RNG_W (world segs) (@w_H segs) W') ((135424 + i) / 8 + 2147450880) 1).
  { intros i Hi. replace ((135424 + i) / 8) with 16928 by (Z.div_mod_to_equations; lia).
    apply decode_rng; [lia | lia |]. intros b Hb. replace b with (16928 + 2147450880) by lia. exact VCMD. }
  (* ---- the run: +0x5e8 .. the call at +0x1118 ---- *)
  replace (lo_arm 1) with 0x5e8 by reflexivity.
  unfold lc_cfg.
  replace (transport_text + 0x5e8) with 0x8184c by reflexivity.
  eapply decode_run.
  { unfold LCK.ms_of_regs.
    assert (G9 : YK11.getr regs' (Z_to_bv 5 9) = w64 (lc_sp1 cx)) by exact R9.
    assert (G23 : YK11.getr regs' (Z_to_bv 5 23) = Z_to_bv 64 (N - 1)) by exact C23.
    assert (G24 : YK11.getr regs' (Z_to_bv 5 24) = Z_to_bv 64 (p + O + 1)) by (rewrite C24; unfold w64; f_equal; lia).
    assert (G25 : YK11.getr regs' (Z_to_bv 5 25) = Z_to_bv 64 (p + O)) by exact C25.
    assert (G26 : YK11.getr regs' (Z_to_bv 5 26) = Z_to_bv 64 2147450880) by exact R26.
    assert (G27 : YK11.getr regs' (Z_to_bv 5 27) = Z_to_bv 64 N) by exact C27.
    rewrite G9, G23, G24, G25, G26, G27.
    exact (op1_run_post (LCK.RNG_W (world segs) (@w_H segs) W') _ _ _ _ _ (w64 (lc_sp1 cx)) _ _ _ _ _ _ _ _ _ _
             mem' p O N M96 M136 R96 R136 MDST MSRC MCMD SDST SSRC SCMD RDST RSRC RCMD RSDST RSSRC RSCMD D Bw HN1 HN26
             HcO Hp0 HPN HRB HSH HRD HRS M48 R48 MLC RLC _ _ _ _ _ _ _ _ _ _ _ _). }
  intros ms' md'' (ms0 & HPOST & EQV) SBM.
  destruct HPOST as (t0' & t1' & t2' & a2' & a3' & s8' & -> & Ha2 & Ha3).
  rewrite (decode_ms_shape _ _ _ _ EQV).
  apply SRr_ret.
  set (regs2 := ms_regs ms').
  (* a register of the state after the run, read off the run's register tree *)
  assert (GR : forall r : bv 5, YK11.getr regs2 r = YK11.getr (ms_regs ms') r) by reflexivity.
  unfold lc_st_bar1. fold D p c Bw.
  exists ly', S', regs2, mem', md'', e. cbv zeta.
  rewrite (op1_frame_vals D Bw c HcN Hn0). cbn [fv_sel fv_send fv_ack fv_retry fv_off fv_len fv_c TOP.fi_off TOP.fi_n].
  fold O N.
  destruct HL as (_ & _ & HSP0 & HFSH0 & HOK0 & He0 & HME0 & _).
  assert (G2 : YK11.getr regs2 (Z_to_bv 5 2) = w64 (lc_sp1 cx))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; exact R2).
  assert (G3 : YK11.getr regs2 (Z_to_bv 5 3) = w64 (as_gp B))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; exact R3).
  assert (G4 : YK11.getr regs2 (Z_to_bv 5 4) = w64 (as_tp B))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; exact R4).
  assert (G8 : YK11.getr regs2 (Z_to_bv 5 8) = w64 (lc_sp0 cx))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; exact R8).
  assert (G9 : YK11.getr regs2 (Z_to_bv 5 9) = w64 (lc_sp1 cx))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G18 : YK11.getr regs2 (Z_to_bv 5 18) = w64 (lc_SH cx))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; exact R18).
  assert (G20 : YK11.getr regs2 (Z_to_bv 5 20) = w64 LF_S4)
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; exact R20).
  assert (G21 : YK11.getr regs2 (Z_to_bv 5 21) = w64 (lo_ops op))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; exact R21).
  assert (G22 : YK11.getr regs2 (Z_to_bv 5 22) = w64 7)
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; exact R22).
  assert (G26 : YK11.getr regs2 (Z_to_bv 5 26) = w64 SHADOW_OFF)
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G10 : YK11.getr regs2 (Z_to_bv 5 10) = w64 (lc_fdst_a (og O N D 0)))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G11 : YK11.getr regs2 (Z_to_bv 5 11) = w64 (lc_fsrc_a (og O N D 0)))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G12 : YK11.getr regs2 (Z_to_bv 5 12) = a2')
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G13 : YK11.getr regs2 (Z_to_bv 5 13) = a3')
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G14 : YK11.getr regs2 (Z_to_bv 5 14) = w64 (r_retry O N D))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G15 : YK11.getr regs2 (Z_to_bv 5 15) = w64 (lc_fcmd (og O N D 0)))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G16 : YK11.getr regs2 (Z_to_bv 5 16) = Z_to_bv 64 (r_S5 p O N))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G17 : YK11.getr regs2 (Z_to_bv 5 17) = w64 (r_len O N D))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G19 : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 (r_S5 p O N + r_len O N D))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  assert (G23 : YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 (r_nr N - r_len O N D))
    by (unfold regs2; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity).
  pose proof (r_send_range O N D) as RS.
  split; [unfold lc_cfg; reflexivity|].
  split; [symmetry; exact Ho|].
  split.
  { (* lc_lcore: the memory is the cut's; the model materialized pages only *)
    split.
    { split.
      { rewrite (YA0o.same_but_materialized_wvb md' md'' SBM).
        apply (W_journalG.ajournal_gx_materialize segs B LAWS decode_segs_low). exact HJ. }
      split; [exact Hfrs|]. split; [exact HlyF|]. split; [exact HPERM|].
      split; [exact G2|]. split; [exact G8|]. split; [exact G9|]. split; [exact G3|]. split; [exact G4|].
      split; [exact Hsp1|]. split; [exact Hsp1al|]. split; [exact HSAV|].
      split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
      split; [exact HFpres|]. split; [exact HFL|]. exact HINP. }
    split; [split; [exact G18 | exact G26]|].
    split; [exact HSP0|]. split; [exact HFSH0|]. split; [exact HOK0|]. split; [exact He0|].
    split; [exact HME0 | exact G21]. }
  split; [exact HTW|].
  split; [exact G10|]. split; [exact G11|].
  split; [replace (YK11.getr regs2 12) with a2' by (symmetry; exact G12); rewrite Ha2; apply Z.mod_small; lia|].
  split; [replace (YK11.getr regs2 13) with a3' by (symmetry; exact G13); exact Ha3|].
  split; [exact G14|]. split; [exact G15|].
  split; [replace (YK11.getr regs2 16) with (Z_to_bv 64 (r_S5 p O N)) by (symmetry; exact G16);
          unfold w64, r_S5; f_equal; lia|].
  split; [exact G17|].
  split; [unfold lc_cur; cbn [TOP.fi_off TOP.fi_n]; split;
          [rewrite G19; unfold w64, r_S5; f_equal; lia | exact G23]|].
  split; [exact G20 | exact G22].
Qed.

End seg1.
