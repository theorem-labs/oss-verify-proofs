From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_latest_frame_c check_latest_frame_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_latest_frame_contract_F (image A, entry 0x843e0, frame 16 bytes), with StepF's step: each access
   side goal is closed from the rng fact of the range it touches.

   The walk (listing DgnTransportList.v, the 52 slots from AF_check_latest_frame):
     0x843e0-0x843e4  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x843e8-0x843f0  a2 = the 8 bytes at GOT_CELL_K, then a3 = the 8 bytes at CELL_K = 0x7fff8000 (asan_cells).
     0x843f4-0x84404  a2 = a0 + 56; a4 = the shadow byte at (a2 >> 3) + 0x7fff8000; bnez a4.
     0x84408-0x84418  a2 = the 8-byte load at a0 + 56 (body_len); a4 = g_cfg; a5 = the 4-byte load at
                      g_cfg + 56 (max_body), zero-extended; bltu a5,a2 to 0x84480.
     0x8441c-0x8442c  a2 = a0 + 41; a5 = the shadow byte of a2; bnez a5 to 0x84488.
     0x84430-0x8443c  a2 = the byte at a0 + 41 (ncmds), zero-extended; a4 = the 4-byte load at g_cfg + 52
                      (max_cmds), sign-extended; bltu a4,a2 to 0x84480; beq a1,a2 to 0x8444c.
     0x84440-0x84448  a1 = the 4-byte load at g_raw, sign-extended; beqz a1 to 0x84480.
     0x8444c-0x8445c  a0 = a0 + 32; a1 = the shadow byte of a0; bnez a1 to 0x84498.
     0x84460-0x84470  a1 = the 4-byte load at M + 84 (host_counter), sign-extended; a0 = the 4-byte load at
                      a0 (send), sign-extended; a1 = the low 32 bits of a1 + a2, sign-extended; bne a0,a1 to 0x84480.
     0x84474-0x8447c  ld ra,8(sp); addi sp,sp,16; ret: the one return.
   The two instrumented checks that can branch (0x84488-0x8448c and 0x84498-0x844a0) load no memory: they mask the
   low 3 bits of the address and compare, then go back to 0x84430 / 0x84460. Both ways past such a check reach the
   same state, so the walk carries on with one script over the two cases (the destructs of SK41 and SK32).

   The paths the premises rule out:
     - 0x844ac (__asan_report_load8): reached when the shadow byte of a0 + 56 is not 0. addressable m (a0 + 56) 8
       covers the byte a0 + 63 of that byte's granule, so the byte is 0 (ka_addr8) and the bnez at 0x84404 falls
       through;
     - 0x84494 (__asan_report_load1): reached when the shadow byte k of a0 + 41 is not 0 and (a0 + 41) mod 8 >= k.
       addressable m (a0 + 41) 1 gives k = 0 or (a0 + 41) mod 8 < k (ka_addr1), so the blt at 0x8448c is taken;
     - 0x844a4 (__asan_report_load4): reached when the shadow byte k of a0 + 32 is not 0 and
       (a0 + 32) mod 8 + 3 >= k. addressable m (a0 + 32) 4 covers the last byte of the access inside its granule,
       which gives k = 0 or (a0 + 32) mod 8 + 3 < k (ka_addr4), so the blt at 0x844a0 is taken;
     - 0x84480 / 0x84484 (__asan_handle_no_return, abort), from the four tests: the model premise
       check_latest_frame_m Bw frame cmds = Some (Bw', tt) gives body_len <= max_body, ncmds <= max_cmds,
       g_raw <> 0 or ncmds = cmds, and send = u32 (host_counter + ncmds), and each test is decided from the member
       values (the bytes of the three put premises) and the world values (tw_at, through tw_bytes_at and the
       ld / lw / lwu load forms of TWorldG).
   The world after: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_LO, G_HARNESS_HI) of the 18 payload ranges (the off_stk premise), so tw_at holds of the same Bw
   (TMAP_A_kept), and the model premise gives Bw' = Bw. *)

(* ---- reading a whole byte list at an address ---- *)

Lemma clf_rd_all : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* the same read at a register whose value is that address *)
Lemma clf_rdw : forall m (w : word) a bs n, bytes_at rsegs m a bs -> length bs = n -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w n = Some bs.
Proof.
  intros m w a bs n H L E. rewrite <- (Z_to_bv_bv_unsigned w), E.
  change (Z_to_bv 64 a) with (wa a). apply clf_rd_all; assumption.
Qed.

Lemma clf_signed0 : forall k : byte, bv_signed k = 0 -> bv_unsigned k = 0.
Proof.
  intros k H. pose proof (byte_range k) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  replace (2 ^ Z.of_N 8) with 256 in H by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* ---- the shadow byte each instrumented check reads, and what the check needs of it ---- *)

Lemma clf_addr1 : forall m a, addressable m a 1 ->
  0 <= a /\ a + 1 <= APPMEM_END /\ app_mem a /\
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\
            (bv_signed k = 0 \/ (a mod 8 < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m a (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP & k & MK & SK).
  rewrite Z.add_0_r in APP, MK, SK. unfold shadow_addr in MK. unfold shadow_ok in SK.
  split; [lia|]. split; [lia|]. split; [exact APP|]. exists k. split; [exact MK | exact SK].
Qed.

(* an 8-byte range holds the last byte of its first granule, so that granule's shadow byte is 0 *)
Lemma clf_addr8 : forall m a, addressable m a 8 ->
  0 <= a /\ a + 8 <= APPMEM_END /\ app_mem a /\
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\ bv_unsigned k = 0.
Proof.
  intros m a (P0 & N0 & PE & AB).
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MB.
  destruct (AB 0 ltac:(lia)) as (APP & _). rewrite Z.add_0_r in APP.
  destruct (AB (7 - a mod 8) ltac:(lia)) as (_ & k & MK & SK).
  assert (E : (a + (7 - a mod 8)) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
  assert (M7 : (a + (7 - a mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  unfold shadow_addr in MK. rewrite E in MK. unfold shadow_ok in SK. rewrite M7 in SK.
  split; [lia|]. split; [lia|]. split; [exact APP|]. exists k. split; [exact MK|].
  destruct SK as [S0 | [S1 S2]]; [apply clf_signed0; exact S0 | lia].
Qed.

(* the last byte of a 4-byte range inside its first granule: byte a + 3, or the granule's byte 7 *)
Lemma clf_addr4 : forall m p, addressable m p 4 ->
  0 <= p /\ p + 4 <= APPMEM_END /\ app_mem p /\
  exists k, mrd rsegs m (wa (p / 8 + ASAN_K)) = Some k /\
            (bv_signed k = 0 \/ p mod 8 + 3 < bv_signed k).
Proof.
  intros m p (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP & k & MK & _). rewrite Z.add_0_r in APP, MK.
  unfold shadow_addr in MK.
  split; [lia|]. split; [lia|]. split; [exact APP|].
  exists k. split; [exact MK|].
  pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as MB.
  set (i := Z.min 3 (7 - p mod 8)).
  assert (Hi : 0 <= i < 4) by (unfold i; lia).
  destruct (AB i Hi) as (_ & ki & MKi & SKi).
  assert (E : shadow_addr (p + i) = p / 8 + ASAN_K).
  { unfold shadow_addr. f_equal. unfold i. clear - MB. Z.div_mod_to_equations. lia. }
  rewrite E in MKi. unfold ASAN_K in MKi, MK. rewrite MK in MKi. injection MKi as Ek. subst ki.
  assert (Em : (p + i) mod 8 = p mod 8 + i).
  { unfold i. clear - MB. Z.div_mod_to_equations. lia. }
  unfold shadow_ok in SKi. rewrite Em in SKi. unfold i in SKi. lia.
Qed.

(* a shadow byte of an application address lies outside a 16-byte frame of application memory *)
Lemma clf_shadow_tp : forall m m' lo hi a k, munch [(lo, hi)] m m' -> lo + 16 = hi ->
  app_mem lo -> app_mem (hi - 1) -> app_mem a ->
  mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (a / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' lo hi a k MU E A1 A2 A3 H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, A3. unfold ASAN_K in *.
  apply (mrd_tp m m' lo hi _ k MU); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact H].
Qed.

(* the signed compare of a small non-negative value with a sign-extended shadow byte (AsanKAProof's lts_low
   covers offsets below 8; the 4-byte check compares the offset plus 3) *)
Lemma clf_lts_small : forall (x : Z) (k : byte), 0 <= x < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

(* ---- the register values the loads leave ---- *)

Lemma clf_zxb_lit8 : forall z, 0 <= z < 256 -> zxb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma clf_sx32_lit : forall z, 0 <= z < 2 ^ 64 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 (bv_swrap 32 z).
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by exact Hz. reflexivity. Qed.

(* the members are put bytes; these are the byte lists the load step reads *)
Lemma clf_put1 : forall z, TW.put 1 z = [Z_to_bv 8 z].
Proof. intros z. rewrite <- TWorldLemmas.le1_put. apply le1_lit_byte. Qed.

Lemma clf_put4 : forall z, TW.put 4 z = le4 (Z_to_bv 64 z).
Proof. intros z. symmetry. apply TWorldLemmas.le4_put. Qed.

Lemma clf_put8 : forall z, TW.put 8 z = le8 (Z_to_bv 64 z).
Proof. intros z. symmetry. apply TWorldLemmas.le8_put. Qed.

(* ---- the 32-bit sign extension of the RV64 psABI (as the plain walk lib/Prog/T/check_latest_frame.v) ---- *)

Lemma clf_swrap32_cases : forall x, 0 <= x < 2 ^ 32 ->
  (x < 2 ^ 31 /\ bv_swrap 32 x = x) \/ (2 ^ 31 <= x /\ bv_swrap 32 x = x - 2 ^ 32).
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  destruct (Z_lt_le_dec x (2 ^ 31)) as [L|L].
  - left. split; [lia|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|].
    rewrite <- (Z.mod_add (x + 2 ^ 31) (-1) (2 ^ 32)) by (vm_compute; discriminate).
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma clf_swrap32_cong : forall x y k, x = y + k * 2 ^ 32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof.
  intros x y k ->. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). f_equal.
  replace (y + k * 2 ^ 32 + bv_half_modulus 32) with (y + bv_half_modulus 32 + k * 2 ^ 32) by lia.
  apply Z.mod_add. vm_compute. discriminate.
Qed.

Lemma clf_swrap32_modx : forall x, bv_swrap 32 (x mod 2 ^ 32) = bv_swrap 32 x.
Proof.
  intros x. apply (clf_swrap32_cong _ _ (- (x / 2 ^ 32))).
  rewrite Z.mod_eq by (vm_compute; discriminate). lia.
Qed.

(* the addw at 0x8446c of the sign-extended host_counter and the zero-extended ncmds is the send value *)
Lemma clf_addw_send : forall hc nc sd, 0 <= nc < 256 -> 0 <= hc < 2 ^ 32 -> sd = DgnSpec.u32 (hc + nc) ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 hc)) + bv_unsigned (Z_to_bv 64 nc))
  = bv_swrap 32 sd.
Proof.
  intros hc nc sd Hnc Hhc ->. rewrite (unsigned_lit nc) by lia.
  unfold DgnSpec.u32. rewrite clf_swrap32_modx.
  destruct (clf_swrap32_cases hc Hhc) as [[Hlt Hq]|[Hge Hq]]; rewrite Hq.
  - rewrite unsigned_lit by lia. reflexivity.
  - rewrite unsigned_lit_wrap.
    rewrite <- (Z.mod_add (hc - 2 ^ 32) 1 (2 ^ 64)) by (vm_compute; discriminate).
    rewrite (Z.mod_small (hc - 2 ^ 32 + 1 * 2 ^ 64)) by lia.
    apply (clf_swrap32_cong _ _ (2 ^ 32 - 1)). lia.
Qed.

(* ---- the two member values the tests compare are in range ---- *)

(* ncmds is one byte of the frame *)
Lemma clf_ncmds_range : forall frame, 0 <= DgnSpec.sf_ncmds (TC.rf frame) < 256.
Proof.
  intros frame. unfold TC.rf, DgnSpec.spec_read_frame.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end);
    cbn [DgnSpec.sf_ncmds]; try lia.
  unfold DgnSpec.byte_at.
  set (l := TW.zs frame).
  assert (H : Forall (fun z => 0 <= z < 256) l).
  { unfold l, TW.zs. apply Forall_map. apply Forall_forall. intros x _. apply byte_range. }
  set (i := Z.to_nat DgnSpec.SPEC_AT_NCMDS).
  destruct (Nat.lt_ge_cases i (length l)) as [HL|HL].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact HL.
  - rewrite nth_overflow by exact HL. lia.
Qed.

Lemma clf_be16_range : forall b p, 0 <= DgnSpec.spec_be16 b p < 65536.
Proof. intros b p. unfold DgnSpec.spec_be16, DgnSpec.u16. apply Z.mod_pos_bound. lia. Qed.

(* body_len is numbytes - 16, with 16 <= numbytes < 2^16 *)
Lemma clf_body_len_range : forall frame, 0 <= DgnSpec.sf_body_len (TC.rf frame) < 2 ^ 16.
Proof.
  intros frame.
  pose proof (clf_be16_range (TW.zs frame) DgnSpec.SPEC_AT_NUMBYTES) as HB.
  unfold TC.rf, DgnSpec.spec_read_frame.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c eqn:? end);
    cbn [DgnSpec.sf_body_len]; unfold DgnSpec.SPEC_HDR in *; try lia.
Qed.

Theorem check_latest_frame_holds_F : check_latest_frame_contract_F.
Proof.
  unfold check_latest_frame_contract_F, CHECK_LATEST_FRAME, CHECK_LATEST_FRAME_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw Bw' fp frame cmds HA0 HA1 HCMDS HFP0 HFP8 BSEND BNCMDS BBLEN HW HM HSTK HLO HOFF CELLS
    APW1 APW2 DGOT DCELL DBLEN ABLEN DNCMDS ANCMDS DSEND ASEND RFR RGOT RCELL RSBLEN RBLEN RMAXB RSNCMDS
    RNCMDS RMAXC RRAW RSSEND RHOST RSEND.
  subst a1.
  (* ---- the model: the four tests that reach the trap are decided, and Bw' = Bw ---- *)
  unfold TC.check_latest_frame_m in HM. cbv zeta in HM.
  match type of HM with context [if ?c then _ else _] => destruct c eqn:C1 end; [discriminate HM|].
  match type of HM with context [if ?c then _ else _] => destruct c eqn:C2 end; [discriminate HM|].
  assert (HB : Bw' = Bw).
  { pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) HM)
      as HBx. cbv beta iota in HBx. symmetry. exact HBx. }
  subst Bw'. clear HM.
  apply orb_false_iff in C1 as [C1a Craw]. apply orb_false_iff in C1a as [Cbody Ccmds].
  apply Z.ltb_ge in Cbody. apply Z.ltb_ge in Ccmds.
  apply negb_false_iff, Z.eqb_eq in C2.
  (* ---- the three members, and the ranges the tests need ---- *)
  pose proof (clf_ncmds_range frame) as Rnc.
  pose proof (clf_body_len_range frame) as Rbl.
  set (nc := DgnSpec.sf_ncmds (TC.rf frame)) in *.
  set (bl := DgnSpec.sf_body_len (TC.rf frame)) in *.
  set (sd := DgnSpec.sf_send (TC.rf frame)) in *.
  clearbody nc bl sd.
  assert (Rsd : 0 <= sd < 2 ^ 32) by (rewrite C2; unfold DgnSpec.u32; apply Z.mod_pos_bound; lia).
  assert (Rmb : 0 <= TW.Cfg_max_body Bw < 2 ^ 32).
  { pose proof (TWorldLemmas.u_at_range Bw TW.A_Cfg_max_body 4) as H.
    change (8 * Z.of_nat 4) with 32 in H. exact H. }
  assert (Rmc : 0 <= TW.Cfg_max_cmds Bw < 2 ^ 32).
  { pose proof (TWorldLemmas.u_at_range Bw TW.A_Cfg_max_cmds 4) as H.
    change (8 * Z.of_nat 4) with 32 in H. exact H. }
  assert (Rhc : 0 <= TW.M_host_counter Bw < 2 ^ 32).
  { pose proof (TWorldLemmas.u_at_range Bw TW.A_M_host_counter 4) as H.
    change (8 * Z.of_nat 4) with 32 in H. exact H. }
  assert (Rraw : -2 ^ 31 <= TW.g_raw Bw < 2 ^ 31).
  { unfold TW.g_raw, TW.s32_at.
    pose proof (TWorldLemmas.u_at_range Bw TW.OFF_g_raw 4) as HR0.
    change (8 * Z.of_nat 4) with 32 in HR0.
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with (2 ^ 32). Z.div_mod_to_equations. lia. }
  pose proof (clf_swrap32_cases _ Rmc) as Dmc.
  pose proof (clf_swrap32_cases _ HCMDS) as Dcm.
  (* ---- the shadow byte of each member load, and fp as the value of a0 ---- *)
  destruct (clf_addr8 m (fp + 56) ABLEN) as (P56 & E56 & APP56 & k56 & MK56 & K56).
  destruct (clf_addr1 m (fp + 41) ANCMDS) as (P41 & E41 & APP41 & k41 & MK41 & SK41).
  destruct (clf_addr4 m (fp + 32) ASEND) as (P32 & E32 & APP32 & k32 & MK32 & SK32).
  unfold APPMEM_END in E56, E41, E32.
  assert (U0 : bv_unsigned a0 = fp) by (rewrite HA0; apply unsigned_lit; lia).
  clear HA0. subst fp.
  (* ---- the world bytes the code reads, as raw memory ---- *)
  assert (LMB : length (TW.sub Bw (TW.OFF_g_cfg + 56) 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.OFF_g_cfg; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.OFF_g_cfg, TW.W_LEN. lia. }
  assert (LMC : length (TW.sub Bw (TW.OFF_g_cfg + 52) 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.OFF_g_cfg; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.OFF_g_cfg, TW.W_LEN. lia. }
  assert (LRW : length (TW.sub Bw (TW.OFF_g_raw + 0) 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.OFF_g_raw; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.OFF_g_raw, TW.W_LEN. lia. }
  assert (LHC : length (TW.sub Bw (TW.OFF_M + 84) 4) = 4%nat).
  { apply TWorldLemmas.length_sub; [unfold TW.OFF_M; lia|].
    rewrite (tw_len TMAP_A _ Bw HW). unfold TW.OFF_M, TW.W_LEN. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 56 4 TMAP_A_ok HW
    TMAP_A_g_cfg ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)) as BMB.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 52 4 TMAP_A_ok HW
    TMAP_A_g_cfg ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)) as BMC.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_g_raw TA_g_raw TW.SZ_g_raw 0 4 TMAP_A_ok HW
    TMAP_A_g_raw ltac:(lia) ltac:(unfold TW.SZ_g_raw; lia)) as BRW.
  pose proof (tw_bytes_at rsegs m TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 84 4 TMAP_A_ok HW
    TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BHC.
  change (TA_g_cfg + 56) with 6156472 in BMB.
  change (TA_g_cfg + 52) with 6156468 in BMC.
  change (TA_g_raw + 0) with 6156512 in BRW.
  change (TA_M + 84) with 6156724 in BHC.
  (* ---- the member bytes in the byte-list forms the load step reads ---- *)
  rewrite clf_put4 in BSEND. rewrite clf_put1 in BNCMDS. rewrite clf_put8 in BBLEN.
  (* keep every bytes_at fact off transport_chunks: they are carried past the ra store by hand *)
  pose proof (conj BSEND (conj BNCMDS (conj BBLEN (conj BMB (conj BMC (conj BRW BHC)))))) as KEEP.
  clear BSEND BNCMDS BBLEN BMB BMC BRW BHC.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ HSTK) as L0.
  unfold off_stk in DGOT, DCELL, DBLEN, DNCMDS, DSEND.
  unfold off_stk, TG.G_HARNESS_LO, TG.G_HARNESS_HI in HOFF.
  unfold GOT_CELL_K, CELL_K, ASAN_K in DGOT, DCELL, RGOT, RCELL.
  unfold shadow_addr, ASAN_K in RSBLEN, RSNCMDS, RSSEND.
  rewrite check_latest_frame_maxbody_at in RMAXB.
  rewrite check_latest_frame_maxcmds_at in RMAXC.
  rewrite check_latest_frame_host_at in RHOST.
  rewrite check_latest_frame_raw_at in RRAW.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat HSTK.
  (* 0x843e0-0x843e4: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct KEEP as (BSEND & BNCMDS & BBLEN & BMB & BMC & BRW & BHC).
  destruct CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  assert (GCK0 : bytes_at rsegs m0 671888 (le8 (wa 707064)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact GCK]).
  assert (CK0 : bytes_at rsegs m0 707064 (le8 (wa 2147450880)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact CK]).
  assert (BSEND0 : bytes_at rsegs m0 (bv_unsigned a0 + 32) (le4 (Z_to_bv 64 sd)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le4; lia | exact BSEND]).
  assert (BNCMDS0 : bytes_at rsegs m0 (bv_unsigned a0 + 41) [Z_to_bv 8 nc])
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [cbn [length]; lia | exact BNCMDS]).
  assert (BBLEN0 : bytes_at rsegs m0 (bv_unsigned a0 + 56) (le8 (Z_to_bv 64 bl)))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact BBLEN]).
  assert (BMB0 : bytes_at rsegs m0 6156472 (TW.sub Bw (TW.OFF_g_cfg + 56) 4))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LMB; lia | exact BMB]).
  assert (BMC0 : bytes_at rsegs m0 6156468 (TW.sub Bw (TW.OFF_g_cfg + 52) 4))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LMC; lia | exact BMC]).
  assert (BRW0 : bytes_at rsegs m0 6156512 (TW.sub Bw (TW.OFF_g_raw + 0) 4))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LRW; lia | exact BRW]).
  assert (BHC0 : bytes_at rsegs m0 6156724 (TW.sub Bw (TW.OFF_M + 84) 4))
    by (apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LHC; lia | exact BHC]).
  pose proof (clf_shadow_tp m m0 _ _ _ k56 MU1 ltac:(lia) APW1 APW2 APP56 MK56) as M56.
  pose proof (clf_shadow_tp m m0 _ _ _ k41 MU1 ltac:(lia) APW1 APW2 APP41 MK41) as M41.
  pose proof (clf_shadow_tp m m0 _ _ _ k32 MU1 ltac:(lia) APW1 APW2 APP32 MK32) as M32.
  unfold ASAN_K in M56, M41, M32.
  clear BSEND BNCMDS BBLEN BMB BMC BRW BHC CK GCK MK56 MK41 MK32.
  (* 0x843e8-0x843ec: a2 = the GOT cell *)
  pose proof (clf_rd_all m0 _ _ 8 GCK0 (length_le8 _)) as RDG.
  step. step. clear RDG.
  (* 0x843f0: a3 = 0x7fff8000 *)
  pose proof (clf_rd_all m0 _ _ 8 CK0 (length_le8 _)) as RDS.
  step. clear RDS.
  (* 0x843f4-0x84400: the instrumented check of the 8-byte load at a0 + 56 *)
  step. gen_addi a0 w56 U56.
  pose proof (rng_sub' _ _ _ (bv_unsigned w56) 8 RBLEN ltac:(lia)) as RW56.
  step. gen_shr w56 g56 G56. rewrite U56 in G56.
  step. gen_addi g56 h56 H56.
  pose proof (rng_sub' _ _ _ (bv_unsigned h56) 1 RSBLEN ltac:(lia)) as RH56.
  pose proof (rdw0 m0 h56 _ _ M56 ltac:(lia)) as R. step. clear R.
  (* 0x84404: the shadow byte is 0, so the error path is not reached *)
  step. if_cases HS56; [exfalso; zify_cond HS56; rewrite ?zxb_u in HS56; lia|].
  (* 0x84408: a2 = body_len *)
  pose proof (clf_rdw m0 w56 _ _ 8 BBLEN0 (length_le8 _) ltac:(lia)) as R. step. clear R.
  (* 0x8440c-0x84414: a4 = g_cfg, a5 = max_body *)
  step. step.
  pose proof (clf_rd_all m0 _ _ 4 BMB0 LMB) as R. step. clear R.
  rewrite lwu_world.
  change (TW.u_at Bw (TW.OFF_g_cfg + 56) 4) with (TW.Cfg_max_body Bw).
  (* 0x84418: max_body < body_len would go to the trap *)
  step. if_cases E1; [exfalso; zify_cond E1; rewrite ?unsigned_lit_wrap in E1;
                      clear - E1 Cbody Rbl Rmb; Z.div_mod_to_equations; lia|].
  (* 0x8441c-0x84428: the instrumented check of the byte load at a0 + 41 *)
  step. gen_addi a0 w41 U41.
  pose proof (rng_sub' _ _ _ (bv_unsigned w41) 1 RNCMDS ltac:(lia)) as RW41.
  step. gen_shr w41 g41 G41. rewrite U41 in G41.
  step. gen_addi g41 h41 H41.
  pose proof (rng_sub' _ _ _ (bv_unsigned h41) 1 RSNCMDS ltac:(lia)) as RH41.
  pose proof (rdw0 m0 h41 _ _ M41 ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 41) 8 ltac:(lia)) as MB41.
  (* 0x8442c: either the shadow byte is 0, or 0x84488-0x8448c compares and goes back to 0x84430 *)
  destruct SK41 as [C41|[C41 C41u]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C41); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k41) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U41, (lts_low ((bv_unsigned a0 + 41) mod 8) k41 MB41),
             (proj2 (Z.ltb_lt _ _) C41); cbn [negb].
  (* 0x84430: a2 = ncmds *)
  all: pose proof (clf_rdw m0 w41 _ _ 1 BNCMDS0 ltac:(cbn [length]; reflexivity) ltac:(lia)) as R;
       step; clear R.
  all: rewrite (clf_zxb_lit8 nc ltac:(lia)).
  (* 0x84434: a4 = max_cmds *)
  all: pose proof (clf_rd_all m0 _ _ 4 BMC0 LMC) as R; step; clear R.
  all: rewrite lw_world.
  all: change (TW.s32_at Bw (TW.OFF_g_cfg + 52)) with (bv_swrap 32 (TW.Cfg_max_cmds Bw)).
  (* 0x84438: max_cmds < ncmds would go to the trap (a max_cmds of 2^31 or more has an unsigned value
     above every byte) *)
  all: step; if_cases E2;
       [exfalso; zify_cond E2; rewrite ?unsigned_lit_wrap in E2;
        destruct Dmc as [[H1 Hq]|[H1 Hq]]; rewrite Hq in E2;
        clear - E2 Ccmds Rnc Rmc; Z.div_mod_to_equations; lia|].
  (* 0x8443c: ncmds = cmds skips the g_raw test; else g_raw <> 0 by the model *)
  all: step; if_cases E3;
       [ | assert (RAW : TW.g_raw Bw <> 0);
           [ apply andb_false_iff in Craw as [Cr|Cr];
             [ apply negb_false_iff in Cr; unfold TC.truth in Cr;
               apply negb_true_iff, Z.eqb_neq in Cr; exact Cr
             | exfalso; apply negb_false_iff, Z.eqb_eq in Cr;
               zify_cond E3; rewrite ?unsigned_lit_wrap in E3;
               destruct Dcm as [[H1 Hq]|[H1 Hq]]; rewrite Hq in E3;
               clear - E3 Cr Rnc H1; Z.div_mod_to_equations; lia ]
           | pose proof (clf_rd_all m0 _ _ 4 BRW0 LRW) as R; step; step; clear R;
             rewrite lw_world;
             change (TW.s32_at Bw (TW.OFF_g_raw + 0)) with (TW.g_raw Bw);
             step; if_cases E4;
             [ exfalso; zify_cond E4; rewrite ?unsigned_lit_wrap in E4;
               clear - E4 RAW Rraw; Z.div_mod_to_equations; lia
             | ] ] ].
  (* 0x8444c-0x8445c: the instrumented check of the 4-byte load at a0 + 32 *)
  all: step; gen_addi a0 w32 U32.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w32) 4 RSEND ltac:(lia)) as RW32.
  all: step; gen_shr w32 g32 G32.
  all: rewrite U32 in G32.
  all: step; gen_addi g32 h32 H32.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h32) 1 RSSEND ltac:(lia)) as RH32.
  all: pose proof (rdw0 m0 h32 _ _ M32 ltac:(lia)) as R; step; clear R.
  all: step.
  all: pose proof (Z.mod_pos_bound (bv_unsigned a0 + 32) 8 ltac:(lia)) as MB32.
  (* 0x8445c: either the shadow byte is 0, or 0x84498-0x844a0 compares and goes back to 0x84460 *)
  all: destruct SK32 as [C32|C32];
       [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C32); cbn [negb]
       | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k32) 0) ltac:(lia)); cbn [negb];
         step; step; step;
         rewrite land7, U32, (clf_lts_small ((bv_unsigned a0 + 32) mod 8 + 3) k32 ltac:(lia)),
                 (proj2 (Z.ltb_lt _ _) C32); cbn [negb] ].
  (* 0x84460-0x84464: a1 = M.host_counter *)
  all: pose proof (clf_rd_all m0 _ _ 4 BHC0 LHC) as R; step; step; clear R.
  all: rewrite lw_world.
  all: change (TW.s32_at Bw (TW.OFF_M + 84)) with (bv_swrap 32 (TW.M_host_counter Bw)).
  (* 0x84468: a0 = send *)
  all: pose proof (clf_rdw m0 w32 _ _ 4 BSEND0 (length_le4 _) ltac:(lia)) as R; step; clear R.
  all: rewrite (clf_sx32_lit sd ltac:(lia)).
  (* 0x8446c: a1 = the low 32 bits of host_counter + ncmds, sign-extended *)
  all: step.
  all: match goal with |- context [bv_swrap 32 (bv_unsigned ?x + bv_unsigned ?y)] =>
         replace (bv_swrap 32 (bv_unsigned x + bv_unsigned y)) with (bv_swrap 32 sd)
           by (symmetry; apply clf_addw_send; [lia | lia | exact C2]) end.
  (* 0x84470: the two registers hold the same value, so the trap is not reached *)
  all: step; if_false.
  (* 0x84474-0x8447c: ld ra; addi sp; ret *)
  all: step; step; step.
  all: apply evtF_done; do 8 eexists; split; [reflexivity|]; split; [exact MU1|]; split; [eassumption|];
       split; [release_frame FR HSTK (bv_unsigned sp); exact HSTK|];
       split; [reflexivity|];
       apply (TMAP_A_kept m m0 _ _ Bw HW MU1);
       unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia.
Qed.

Print Assumptions check_latest_frame_holds_F.
