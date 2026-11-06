(* Walk of send_control (transport/src/diginet_session.c:97-109) in the ubsan image: 0x16bf0, 240 bytes, own frame
   128, send_raw inlined, for the contract of U/Prog/T/send_control_c.v. It writes h (numbytes/sum 0, the host
   counter, ack_counter, retry 0, cmd, num_commands 0) at sp + 12, builds the 60-byte f at sp + 28 with
   diginet_frame_build (body NULL, length 0: the wide contract), copies f to keep and stores n in *keep_len when keep
   is not NULL (memcpy), and sends f through s->io.send (io_send), counting stats.tx_frames when it answers 0.
   The UBSan traps (unimp at 0x16cdc) are not reached:
   - 0x16c14 bnez (s & 7): s = &g_s = W_BASE_UBSAN + OFF_g_s is 8-aligned, a closed computation;
   - 0x16c78 beqz s1 (keep_len NULL) and 0x16c80 bnez (keep_len & 7): the contract's 0 < keep_len (arg_blk) and
     keep_len mod 8 = 0, on the path where keep is not NULL.
   The model's Some (send_control_m, TModel/TSess.v) gives the rest: the sum mode decides the build's code (-1 for a
   mode other than 0 and 1, which send_control returns at once), call_send's test gives s->io.send = io_send, and
   io_send_m's Some gives that call; io_send answers 0 or -EIO (TModel/TIoSendFail.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TNeed TSess0 TCb TSess
  TIoSendFail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c diginet_frame_build_c diginet_frame_build_w_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC io_send_c send_control_c.
Import ListNotations.
Open Scope Z_scope.

(* A branch whose condition is a closed term. *)
Ltac sc_closed v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* The model's code of the build with no body is the wide contract's. *)
Lemma sc_build_code : forall mode, diginet_frame_build_code [] 60 mode = build_code_w [] 60 mode.
Proof.
  intros mode. unfold diginet_frame_build_code, build_code_w. rewrite lib_build_code_eq.
  destruct (mode =? 0), (mode =? 1); reflexivity.
Qed.

Lemma sc_code60 : build_code [] 60 = 60.
Proof. vm_compute. reflexivity. Qed.

(* A 32-bit value sign-extended to the register stores its own four bytes. *)
Lemma sc_le4_swrap : forall x, le4 (Z_to_bv 64 (bv_swrap 32 x)) = Z_to_le_bytes 4 x.
Proof.
  intros x. rewrite le4_put. unfold put.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 x) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 x 32) by lia.
  f_equal. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* A one-byte store of a register (sb): the kit's store aftermath (Lib/Step.v cell_of_bytes, its le1 case) writes
   the cell C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))); its byte is b8 z. *)
Lemma sc_b8 : forall z, 0 <= z < 2 ^ 64 -> Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = b8 z.
Proof. intros z Hz. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac sc_sb :=
  repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => rewrite (sc_b8 z) in H by lia end.


(* Cells of a frame split in two at a cell boundary (U/Prog/diginet_body_check.v ubc_rw_app). *)
Lemma sc_rw_app : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1. rewrite cells_size_app in Hl, Hw.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

(* send_control's 128-byte frame after the stores of 0x16bf4 .. 0x16c38: 12 bytes, the zero numbytes/sum word of h,
   the 12 bytes of h that diginet_frame_build reads (hp + 4 .. hp + 16), the 60-byte f, the saved registers. *)
Lemma sc_frame : forall m A j0 v0 v1 v2 v3 b1 b2 X w3 w2 w1 w0 wr,
  rw_cells rsegs m A [CB 12 j0; C4 v0; C4 v1; C4 v2; C2 v3; C1 b1; C1 b2; CB 60 X; C8 w3; C8 w2; C8 w1; C8 w0; C8 wr] ->
  rw_cells rsegs m A [CB 12 j0; C4 v0] /\
  rw_cells rsegs m (A + 16) [C4 v1; C4 v2; C2 v3; C1 b1; C1 b2] /\
  rw_cells rsegs m (A + 28) [CB (length X) X] /\ length X = 60%nat /\
  rw_cells rsegs m (A + 88) [C8 w3; C8 w2; C8 w1; C8 w0; C8 wr].
Proof.
  intros m A j0 v0 v1 v2 v3 b1 b2 X w3 w2 w1 w0 wr H.
  change (rw_cells rsegs m A ([CB 12 j0; C4 v0] ++ [C4 v1; C4 v2; C2 v3; C1 b1; C1 b2] ++
                              [CB 60 X] ++ [C8 w3; C8 w2; C8 w1; C8 w0; C8 wr])) in H.
  apply sc_rw_app in H. destruct H as [H1 H].
  apply sc_rw_app in H. destruct H as [H2 H].
  apply sc_rw_app in H. destruct H as [H3 H4].
  cbn [cells_size csize Nat.add] in H2, H3, H4.
  pose proof H3 as [[[LX _] _] _]. cbn [cell_wf] in LX.
  split; [exact H1|]. split; [exact H2|]. split; [|split; [exact LX|]].
  - rewrite LX. replace (A + 28) with (A + Z.of_nat 16 + Z.of_nat 12) by lia. exact H3.
  - replace (A + 88) with (A + Z.of_nat 16 + Z.of_nat 12 + Z.of_nat 60) by lia. exact H4.
Qed.

Lemma sc_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma sc_bytes_nil : forall m a, 0 <= a <= 2 ^ 64 -> bytes_at rsegs m a [].
Proof. intros m a H. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

(* The 12 bytes of h at hp + 4 as the wide contract of diginet_frame_build reads them. *)
Lemma sc_hdr : forall hc ack cmd,
  cells_bytes [C4 (Z_to_bv 64 (bv_swrap 32 hc)); C4 (Z_to_bv 64 (bv_swrap 32 ack)); C2 (Z_to_bv 64 0);
               C1 (b8 cmd); C1 (b8 0)] =
  Z_to_le_bytes 4 hc ++ Z_to_le_bytes 4 ack ++ Z_to_le_bytes 2 0 ++ [b8 cmd; b8 0].
Proof. intros. cbn [cells_bytes cbytes app]. rewrite !sc_le4_swrap. reflexivity. Qed.

(* The stack from lo to sp again: below the frame, then the frame's four pieces. *)
Lemma sc_stk5 : forall m lo s a b c d,
  lo <= s + -128 ->
  stk rsegs m lo (s + -128) ->
  stk rsegs m (s + -128) a -> a = s + -112 ->
  stk rsegs m (s + -112) b -> b = s + -100 ->
  stk rsegs m (s + -100) c -> c = s + -40 ->
  stk rsegs m (s + -40) d -> d = s ->
  stk rsegs m lo s.
Proof.
  intros m lo s a b c d L H0 H1 Ea H2 Eb H3 Ec H4 Ed. subst a b c d.
  eapply stk_merge; [|exact H4|lia]. eapply stk_merge; [|exact H3|lia].
  eapply stk_merge; [|exact H2|lia]. eapply stk_merge; [exact H0|exact H1|lia].
Qed.

(* A branch whose condition the context decides (U/Prog/diginet_frame_parse.v br). *)
Ltac sc_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec]
  end.

Lemma sc_cb_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs H. apply sc_bytes in H. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

(* memcpy filled the cell [p, p + n): the stack [lo, hi) stays readable and writable wherever p lies. *)
Lemma sc_stk_cell : forall m m' lo hi p n bs,
  stk rsegs m lo hi -> munch [(p, p + Z.of_nat n)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' p [CB n bs] -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi p n bs (H1 & H2 & H) MU WMo [[Hwf (Hp & Hl & HB)] _].
  cbn [cells_wf cell_wf cells_bytes cbytes] in Hwf, Hl, HB. rewrite app_nil_r in Hl, HB.
  destruct Hwf as [Hlen _].
  split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hv (b & Hb)]. split; [apply WMo; exact Hv|].
  destruct (Z_le_gt_dec p a) as [L1|L1]; [destruct (Z_lt_ge_dec a (p + Z.of_nat n)) as [L2|L2]|].
  - specialize (HB (Z.to_nat (a - p)) ltac:(lia)).
    replace (p + Z.of_nat (Z.to_nat (a - p))) with a in HB by lia.
    rewrite HB. destruct (nth_error bs (Z.to_nat (a - p))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

(* *keep_len = n: the 8-byte cell the store left, as the contract's byte cell. *)
Lemma sc_c8 : forall m A v, rw_cells rsegs m A [C8 v] -> rw_cells rsegs m A [CB 8 (le8 v)].
Proof.
  intros m A v H. pose proof (rw_cells_merge rsegs m A [] [C8 v] [] H) as H'.
  cbn [app cells_size cells_bytes cbytes csize Nat.add] in H'. rewrite app_nil_r in H'. exact H'.
Qed.

Lemma sc_nil_l : forall (l d : list byte), length l = 60%nat -> match l with [] => d | _ :: _ => l end = l.
Proof. intros l d H. destruct l; [discriminate H | reflexivity]. Qed.

Lemma sc_nil_r : forall (l d e : list byte), length l = 60%nat -> match l with [] => d | _ :: _ => e end = e.
Proof. intros l d e H. destruct l; [discriminate H | reflexivity]. Qed.

(* stats.tx_frames++ leaves g_fail_next alone. *)
Lemma sc_gf_tx : forall B v, length B = Z.to_nat W_LEN -> g_fail_next (set_S_stats_tx_frames B v) = g_fail_next B.
Proof.
  intros B v L. unfold set_S_stats_tx_frames, g_fail_next.
  apply u_at_upd_out; unfold A_S_stats_tx_frames, OFF_g_fail_next, OFF_g_s; rewrite ?length_put, ?L; unfold W_LEN; lia.
Qed.

Theorem send_control_holds :
  diginet_frame_build_contract_w -> io_send_contract -> memcpy_contract -> send_control_contract.
Proof.
  intros FB IOS MEMCPY.
  unfold diginet_frame_build_contract_w, DIGINET_FRAME_BUILD in FB.
  unfold io_send_contract, io_send_ENTRY, io_send_FRAME in IOS.
  unfold send_control_contract, send_control_ENTRY, send_control_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    cmd ack kp klp r K KL f B B' TF A0 A1 A2 A3 A4 HC HA KP WM GF HM SP16 ST LO WO MI.
  subst a0 a1 a2 a3 a4.
  unfold w_off_stack in WO.
  wk_facts.
  assert (EO : OFF_g_s = 1648) by reflexivity.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (Z.of_N 64) with 64 in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
  pose proof (wmono_refl rsegs m) as WMO.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* keep = NULL (close, on_data), or wake's e2 / e2_len *)
  destruct KP as [K0 | (KC & KA & KLC & KLA & KL8 & KS)].
  1: subst kp; pose proof (munch_refl [(bv_unsigned sp - 640, bv_unsigned sp);
                                      (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  2: destruct KA as (KA0 & KA1 & KA2 & KA3); destruct KLA as (KLA0 & KLA1 & KLA2 & KLA3);
     unfold off_world in KA2, KLA2; unfold off_window in KA3, KLA3; unfold blk_sep in KS;
     pose proof (munch_refl [(bv_unsigned sp - 640, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN);
                             (kp, kp + 60); (klp, klp + 8)] m) as MU.
  all: carve_frame 128%nat ST.
  (* 0x16bf0 .. 0x16c10: the frame, the saved registers, s0 = s, h.numbytes/sum = 0 *)
  all: do 9 step.
  (* 0x16c14 bnez a0 (s & 7): s = &g_s is 8-aligned *)
  all: step; sc_closed false.
  (* 0x16c18 .. 0x16c20: mv s1,a4; mv s2,a3; lw a0,160(s0) = host_counter *)
  all: do 3 step.
  (* 0x16c24 sb zero,27(sp) *)
  all: step; sc_sb.
  (* 0x16c28 lw a7,20(s0) = cfg.sum_mode; 0x16c2c sw a0,16(sp); 0x16c30 sw a2,20(sp); 0x16c34 sh zero,24(sp) *)
  all: do 4 step.
  (* 0x16c38 sb a1,26(sp) *)
  all: step; sc_sb.
  (* 0x16c3c .. 0x16c54: the arguments of diginet_frame_build *)
  all: do 7 step.
  (* the frame's pieces, the world bytes the build reads, the stack window of the build *)
  all: apply sc_frame in FR; destruct FR as (FR0 & HDR & OUT & LX & SAV).
  all: replace (bv_unsigned sp + -128 + 16) with (bv_unsigned sp + -112) in HDR by lia.
  all: replace (bv_unsigned sp + -128 + 28) with (bv_unsigned sp + -100) in OUT by lia.
  all: replace (bv_unsigned sp + -128 + 88) with (bv_unsigned sp + -40) in SAV by lia.
  all: apply (stk_split _ _ _ (bv_unsigned sp + -368)) in ST; [destruct ST as [STa STb] | lia].
  all: assert (HCR : 0 <= u_at B 1808 4 < 2 ^ 32) by (pose proof (u_at_range B 1808 4) as H; exact H).
  all: assert (LB : length B = Z.to_nat W_LEN) by (eapply wm_len; exact WM).
  all: assert (LDM : length (S_desk_mac B) = 6%nat)
         by (unfold S_desk_mac, A_S_desk_mac, OFF_g_s; apply length_sub; [lia | rewrite LB; wk_side]).
  all: assert (LSM : length (S_cfg_host_mac B) = 6%nat)
         by (unfold S_cfg_host_mac, A_S_cfg_host_mac, OFF_g_s; apply length_sub; [lia | rewrite LB; wk_side]).
  all: assert (BDM : bytes_at rsegs _ (W_BASE_UBSAN + OFF_g_s + 120) (S_desk_mac B))
         by (unfold S_desk_mac, A_S_desk_mac;
             apply (wm_src rsegs W_BASE_UBSAN _ B); [exact WM | lia | unfold OFF_g_s; lia | wk_side]).
  all: assert (BSM : bytes_at rsegs _ (W_BASE_UBSAN + OFF_g_s) (S_cfg_host_mac B))
         by (unfold S_cfg_host_mac, A_S_cfg_host_mac;
             apply (wm_src rsegs W_BASE_UBSAN _ B); [exact WM | lia | unfold OFF_g_s; lia | wk_side]).
  (* 0x16c58 jal diginet_frame_build (sp + 28, 60, &s->desk_mac, &s->cfg.host_mac, &h, NULL, 0, s->cfg.sum_mode) *)
  all: step.
  all: replace (Z_to_bv 64 60) with (Z_to_bv 64 (Z.of_nat (length (skipn 12 (skipn 16
         (firstn 88 (firstn 96 (firstn 104 (firstn 112 (firstn 120 junk)))))))))) by (rewrite LX; reflexivity).
  all: pose proof HDR as HDRc.
  all: change (s32_at B 1808) with (bv_swrap 32 (u_at B 1808 4)) in HDR.
  all: apply sc_bytes in HDR; rewrite sc_hdr in HDR.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply FB with (out := bv_unsigned sp + -100) (dst := W_BASE_UBSAN + OFF_g_s + 120)
        (src := W_BASE_UBSAN + OFF_g_s) (hp := bv_unsigned sp + -116) (body := 0) (mode := s32_at B 1668)
        (lo := bv_unsigned sp + -368) (send := u_at B 1808 4) (ack := ack) (retry := 0) (cmd := cmd) (ncmds := 0)
        (dmac := S_desk_mac B) (smac := S_cfg_host_mac B) (bb := []);
      [ lia | unfold OFF_g_s; lia | unfold OFF_g_s; lia | lia | right; reflexivity | apply s32_range
      | Z.div_mod_to_equations; lia | exact HCR | exact HA | lia | exact HC | lia | lia
      | exact LDM | exact BDM | exact LSM | exact BSM
      | replace (bv_unsigned sp + -116 + 4) with (bv_unsigned sp + -112) by lia; exact HDR
      | apply sc_bytes_nil; lia | exact OUT
      | cbn [length Z.of_nat]; unfold OFF_g_s; lia | cbn [length Z.of_nat]; unfold OFF_g_s; lia
      | cbn [length Z.of_nat]; unfold OFF_g_s; lia | cbn [length Z.of_nat]; unfold OFF_g_s; lia
      | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STb | lia | rewrite Hsp; lia
      | rewrite Hsp; cbn [length Z.of_nat]; unfold OFF_g_s; lia | rewrite Hsp; cbn [length Z.of_nat]; unfold OFF_g_s; lia
      | rewrite Hsp; cbn [length Z.of_nat]; unfold OFF_g_s; lia | rewrite Hsp; cbn [length Z.of_nat]; unfold OFF_g_s; lia
      | rewrite Hsp; cbn [length Z.of_nat]; unfold OFF_g_s; lia | exact MI ]
    | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2 & OUT2);
      subst ms'; rewrite Hsp in MUc, ST2;
      transport_after_call rsegs mm m2 MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv rsegs mm |- _ => clear H end; try clear mm ] end.
  all: rewrite (ret_pc_even 93276) by (first [lia | reflexivity]).
  all: pose proof (stk_merge _ _ _ _ _ STa ST2 ltac:(lia)) as ST; clear STa ST2.
  all: rewrite LX in OUT2 |- *. all: change (Z.of_nat 60) with 60.
  all: revert OUT2 LX; generalize (skipn 12 (skipn 16 (firstn 88 (firstn 96 (firstn 104 (firstn 112 (firstn 120 junk)))))))
         as X; intros X OUT2 LX.
  (* the model: the build's code is build_code_w [] 60 mode *)
  all: unfold send_control_m in HM; cbv zeta in HM.
  all: unfold TSess0.DIGINET_MIN_FRAME_LEN in HM.
  all: change (S_cfg_sum_mode B) with (s32_at B 1668) in HM.
  all: rewrite sc_build_code in HM.
  (* 0x16c5c mv s3,a0; 0x16c60 bltz a0 (the build failed) *)
  all: destruct (orb (s32_at B 1668 =? 0) (s32_at B 1668 =? 1)) eqn:MD;
       assert (BC : build_code_w [] 60 (s32_at B 1668) =
                    if orb (s32_at B 1668 =? 0) (s32_at B 1668 =? 1) then 60 else -1)
         by (unfold build_code_w; rewrite sc_code60; reflexivity);
       rewrite MD in BC; rewrite BC in HM |- *;
       step; step; first [sc_closed true | sc_closed false];
       [ idtac
       | (* a sum mode other than 0 and 1: diginet_frame_build answers -1 (DIGINET_E_ARG) before it writes
            anything, send_control returns it at once and keep is left alone *)
         change (-1 <? 0) with true in HM; cbv iota in HM; injection HM as EB Er Ef; subst B' r f;
         pose proof (stk_of_rw_cells rsegs _ _ _ FR0) as S0; pose proof (stk_of_rw_cells rsegs _ _ _ HDRc) as S1;
         pose proof (stk_of_rw_cells rsegs _ _ _ OUT2) as S2; pose proof (stk_of_rw_cells rsegs _ _ _ SAV) as S3;
         cbn [cells_size csize Nat.add] in S0, S1, S2, S3;
         (* 0x16cbc .. 0x16cd8: a0 = s3, the saved registers back, the frame popped, ret *)
         do 8 step;
         apply evt_done; unfold QQ; do 15 eexists; split; [reflexivity|];
         split; [ first [ (cbn [Z.eqb app]; exact MU)
                        | (replace (kp =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbn [app]; exact MU) ] |];
         split; [exact WMO|]; split; [assumption|];
         split; [eapply sc_stk5; [ | exact ST | exact S0 | | exact S1 | | exact S2 | | exact S3 | ]; lia |];
         split; [exact WM|]; split; [exact GF|];
         first [ (left; reflexivity) | (right; split; assumption) ] ].
  (* sum mode 0 or 1: the build wrote the 60 bytes of the model's frame f into the local f *)
  all: change (60 <? 0) with false in HM; cbv iota in HM.
  all: destruct (send_raw_m _ _ _ _) as [[B1 r1]|] eqn:SR; [|discriminate HM].
  all: injection HM as EB Er Ef; subst B' r.
  all: unfold send_raw_m, call_send in SR.
  all: destruct (S_io_send B =? ti_io_send timg_ubsan) eqn:SE; [|discriminate SR].
  all: apply Z.eqb_eq in SE.
  all: rewrite Ef in SR.
  all: destruct (io_send_m timg_ubsan B f) as [[B2 r2]|] eqn:IO; [|discriminate SR].
  all: assert (MD01 : s32_at B 1668 = 0 \/ s32_at B 1668 = 1)
         by (apply orb_true_iff in MD; destruct MD as [M|M]; apply Z.eqb_eq in M; [left|right]; exact M).
  all: assert (OF : build_out_w (S_desk_mac B) (S_cfg_host_mac B) (u_at B 1808 4) ack 0 cmd 0 [] (s32_at B 1668) X = f)
         by (unfold build_out_w; cbv zeta; rewrite LX; change (Z.of_nat 60) with 60; rewrite BC;
             change (0 <=? 60) with true; cbv iota; change (Z.to_nat 60) with 60%nat;
             rewrite skipn_all2 by lia; rewrite app_nil_r;
             rewrite <- Ef; rewrite (frame_build_bytes _ _ _ _ _ _ _ _ _ MD01); reflexivity).
  all: rewrite OF in OUT2.
  all: assert (LF : length f = 60%nat)
         by (rewrite <- Ef, (frame_build_bytes _ _ _ _ _ _ _ _ _ MD01);
             apply Nat2Z.inj; rewrite (length_build_frame _ _ _ _ _ _ _ _ _ LDM LSM); reflexivity).
  (* 0x16c64 beqz s2 (keep): taken for NULL *)
  all: step.
  all: lazymatch goal with _ : rw_cells _ _ _ [CB 8 _] |- _ => sc_br false | _ => sc_closed true end.
  (* keep is wake's e2: memcpy (keep, f, n), then *keep_len = n *)
  all: lazymatch goal with
       | _ : rw_cells _ _ _ [CB 8 _] |- _ =>
           assert (HL7 : Z.land klp 7 = 0)
             by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; exact KL8);
           (* 0x16c68 .. 0x16c74: addi a1,sp,28; mv a0,s2; mv a2,s3; jal memcpy *)
           do 4 step;
           lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             eapply evt_cut;
             [ eapply MEMCPY with (src := f) (junk := K);
               [ rewrite (unsigned_lit (bv_unsigned sp + -100)) by lia; exact (sc_cb_bytes _ _ _ _ OUT2)
               | change (bv_unsigned (Z_to_bv 64 60)) with 60; rewrite LF; reflexivity
               | rewrite (unsigned_lit kp) by lia; exact KC
               | rewrite (unsigned_lit kp), (unsigned_lit (bv_unsigned sp + -100)) by lia;
                 change (bv_unsigned (Z_to_bv 64 60)) with 60; lia
               | assumption ]
             | intros ms' PO; unfold memcpy_post in PO;
               destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m3 &
                               Eq & MUc & WMc & MI3 & KC3 & SRC3);
               subst ms'; clear SRC3;
               rewrite (unsigned_lit kp) in MUc, KC3 by lia;
               change (bv_unsigned (Z_to_bv 64 60)) with 60 in MUc, KC3; change (Z.to_nat 60) with 60%nat in KC3;
               pose proof (sc_stk_cell _ _ _ _ _ 60%nat _ ST MUc WMc KC3) as ST3;
               clear KC ST;
               transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc;
               try match goal with H : mem_inv rsegs mm |- _ => clear H end; try clear mm;
               rename ST3 into ST ]
           end;
           rewrite (ret_pc_even 93304) by (first [lia | reflexivity]);
           (* 0x16c78 beqz s1: keep_len is not NULL *)
           step; sc_br false;
           (* 0x16c7c andi a0,s1,7; 0x16c80 bnez a0: keep_len is 8-aligned *)
           step; rewrite (unsigned_lit klp) by lia; rewrite HL7; step; sc_closed false;
           (* 0x16c84 sd s3,0(s1): *keep_len = n *)
           step
       | _ => idtac
       end.
  (* 0x16c88 ld a0,64(s0) = s->io.ctx; 0x16c8c ld a3,72(s0) = s->io.send, which call_send says is io_send *)
  all: do 2 step.
  all: change (u_at B 1720 8) with (S_io_send B); rewrite SE; change (ti_io_send timg_ubsan) with 84012.
  (* 0x16c90 addi a1,sp,28; 0x16c94 mv a2,s3; 0x16c98 jalr a3: io_send (s->io.ctx, f, n) *)
  all: do 3 step.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply IOS with (lo := lo) (B := B) (B' := B2) (r := r2) (frame := f) (p := bv_unsigned sp + -100);
      [ reflexivity | rewrite LF; reflexivity | lia | exact (sc_cb_bytes _ _ _ _ OUT2)
      | unfold io_send_frame_at, off_world; rewrite LF; lia
      | rewrite LF; lia
      | unfold off_window; rewrite Hsp; lia
      | exact GF | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | assumption | exact WM | exact IO ]
    | intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m4 &
                  Eq & MUc & WMc & MI4 & ST4 & WM4);
      subst ms'; rewrite Hsp in MUc, ST4;
      pose proof (io_send_m_fail_next _ _ _ _ _ IO LB) as GF2;
      pose proof (wm_len _ _ _ _ WM4) as LB2;
      clear WM ST;
      transport_after_call rsegs mm m4 MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv rsegs mm |- _ => clear H end; try clear mm ] end.
  all: rewrite (ret_pc_even 93340) by (first [lia | reflexivity]).
  (* io_send answers 0 or -EIO *)
  all: destruct (io_send_m_ret _ _ _ _ _ IO) as [R | R]; subst r2.
  all: first [ replace (0 =? 0) with true in SR by reflexivity | replace (- EIO =? 0) with false in SR by reflexivity ].
  all: cbv iota in SR; injection SR as E1 E2; subst B1 r1.
  (* 0x16c9c mv s3,a0; 0x16ca0 bnez a0 *)
  all: step; step; first [ sc_closed true | sc_closed false ].
  (* 0x16ca4 .. 0x16cb8 on 0: li s3,0; s->stats.tx_frames++ *)
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 93348) _ _ _ _) => do 6 step | _ => idtac end.
  all: pose proof (stk_of_rw_cells rsegs _ _ _ FR0) as S0; pose proof (stk_of_rw_cells rsegs _ _ _ HDRc) as S1;
       pose proof (stk_of_rw_cells rsegs _ _ _ OUT2) as S2; pose proof (stk_of_rw_cells rsegs _ _ _ SAV) as S3;
       cbn [cells_size csize Nat.add] in S0, S1, S2, S3.
  (* 0x16cbc .. 0x16cd8: a0 = s3, the saved registers back, the frame popped, ret *)
  all: do 8 step.
  all: apply evt_done; unfold QQ; do 15 eexists; split; [reflexivity|].
  all: split; [ first [ (cbn [Z.eqb app]; exact MU)
                      | (replace (kp =? 0) with false by (symmetry; apply Z.eqb_neq; lia); cbn [app]; exact MU) ] |].
  all: split; [exact WMO|]; split; [assumption|].
  all: split; [eapply sc_stk5; [ | exact ST4 | exact S0 | | exact S1 | | exact S2 | | exact S3 | ]; lia |].
  (* the world: io_send's, with stats.tx_frames + 1 when it answered 0 *)
  all: split; [ first [ exact WM4
                      | (replace (set_S_stats_tx_frames B2 (u64 (S_stats_tx_frames B2 + 1)))
                           with (upd B2 19840 (put 8 (u_at B2 19840 8 + 1)))
                           by (unfold set_S_stats_tx_frames, S_stats_tx_frames, u64; rewrite put_mod64 by lia;
                               reflexivity);
                         exact WMw) ] |].
  (* io_send cleared g_fail_next *)
  all: split; [ first [ (rewrite GF2; lia) | (rewrite sc_gf_tx by exact LB2; rewrite GF2; lia) ] |].
  (* keep holds f and *keep_len = 60 *)
  all: first [ (left; reflexivity)
             | (right; apply sc_c8 in KLC; rewrite le8_put in KLC;
                rewrite (sc_nil_l f K LF), (sc_nil_r f KL _ LF), LF; split; [exact KC3 | exact KLC]) ].
Qed.
