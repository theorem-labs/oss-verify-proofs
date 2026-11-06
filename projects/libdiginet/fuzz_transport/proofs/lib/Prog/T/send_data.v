(* send_data (transport/src/diginet_session.c:388-401) at 0x170cc in the plain image, 47 instructions, FRAME 592.
   The binary inlines inflight_start (:111-117) and send_raw (:88-94). It calls diginet_frame_build (:393), whose
   out cell is s->inflight_frame INSIDE the world (a two-span footprint: the callee's 240-byte stack window and the
   out cell), and then io_send through the world cell g_s.io.send (:400). The local struct diginet_header h lives at
   sp + 8 of this frame; the six stores at 0x170f8 .. 0x17114 fill it (send_counter at h+4, ack 0, retry 0,
   cmd DIGINET_CMD_DATA, num_commands (uint8_t)ncmds). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem
  TNeed TSess0 TCb TSess TIoSendFail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_build_c diginet_frame_build_w_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP TContract TSessC WMem io_send_c send_data_c.
Import ListNotations.
Open Scope Z_scope.

(* ==== build-independent list and arithmetic facts ==== *)

Lemma put_cong32 : forall u v, u mod 2 ^ 32 = v mod 2 ^ 32 -> put 4 u = put 4 v.
Proof.
  intros u v H. unfold put.
  rewrite <- (Z_to_le_bytes_mod 4 u 32) by (cbn; lia). rewrite H.
  apply Z_to_le_bytes_mod. cbn; lia.
Qed.

Lemma put_cong64 : forall u v, u mod 2 ^ 64 = v mod 2 ^ 64 -> put 8 u = put 8 v.
Proof.
  intros u v H. unfold put.
  rewrite <- (Z_to_le_bytes_mod 8 u 64) by (cbn; lia). rewrite H.
  apply Z_to_le_bytes_mod. cbn; lia.
Qed.

Lemma swrap32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma skipn_split : forall (Y : list byte) n j, (j <= n)%nat -> (n <= length Y)%nat ->
  skipn j Y = skipn j (firstn n Y) ++ skipn n Y.
Proof.
  intros Y n j Hj Hn. rewrite <- (firstn_skipn n Y) at 1.
  rewrite skipn_app, length_firstn.
  replace (Nat.min n (length Y)) with n by lia.
  replace (j - n)%nat with 0%nat by lia. cbn [skipn]. reflexivity.
Qed.

(* Writing v and then the bytes that were already behind it changes only v's span. *)
Lemma upd_app_tail : forall (X v : list byte) k n,
  0 <= k -> (Z.to_nat k + n <= length X)%nat -> (length v <= n)%nat ->
  upd X k (v ++ skipn (length v) (sub X k n)) = upd X k v.
Proof.
  intros X v k n Hk Hn Hv.
  assert (LY : length (skipn (Z.to_nat k) X) = (length X - Z.to_nat k)%nat) by apply length_skipn.
  assert (LT : length (v ++ skipn (length v) (sub X k n)) = n).
  { rewrite length_app, length_skipn. unfold sub. rewrite length_firstn, LY. lia. }
  unfold upd. rewrite LT. f_equal. rewrite <- app_assoc. f_equal. unfold sub.
  replace (Z.to_nat k + n)%nat with (n + Z.to_nat k)%nat by lia.
  replace (Z.to_nat k + length v)%nat with (length v + Z.to_nat k)%nat by lia.
  rewrite <- !skipn_skipn.
  symmetry. apply skipn_split; [lia | rewrite LY; lia].
Qed.

(* the bytes of a run of cells inside an rw_cells fact *)
Lemma cells_bytes_at : forall segs m A pre mid post,
  rw_cells segs m A (pre ++ mid ++ post) -> cells_wf pre ->
  bytes_at segs m (A + Z.of_nat (cells_size pre)) (cells_bytes mid).
Proof.
  intros segs m A pre mid post H Hp. destruct H as [[Hwf Hb] _].
  rewrite !cells_bytes_app in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hp.
  apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

(* an 8-byte cell the kit made from a store, back to a CB cell that a later 4-byte store can split *)
Lemma c8_to_cb : forall segs m A c0 (v : word) y,
  rw_cells segs m A (c0 :: C8 v :: y) -> rw_cells segs m A (c0 :: CB 8 (le8 v) :: y).
Proof.
  intros segs m A c0 v y H.
  pose proof (rw_cells_merge segs m A [c0] [C8 v] y H) as H2.
  cbn [cells_size cells_bytes csize cbytes app] in H2. rewrite app_nil_r in H2. exact H2.
Qed.

(* ==== diginet_frame_build's code, as the wide contract and the model state it ==== *)

Lemma bcw_eq : forall body cap mode, build_code_w body cap mode = diginet_frame_build_code body cap mode.
Proof.
  intros body cap mode. unfold build_code_w, diginet_frame_build_code. rewrite lib_build_code_eq.
  destruct ((mode =? 0) || (mode =? 1)); reflexivity.
Qed.

Lemma bc_mode : forall body cap mode, 0 <= diginet_frame_build_code body cap mode -> mode = 0 \/ mode = 1.
Proof.
  intros body cap mode H. unfold diginet_frame_build_code in H.
  destruct ((mode =? 0) || (mode =? 1)) eqn:E; cbn [negb] in H.
  - apply orb_true_iff in E. destruct E as [E|E]; apply Z.eqb_eq in E; auto.
  - lia.
Qed.

Lemma bc_val : forall body cap mode, 0 <= diginet_frame_build_code body cap mode ->
  diginet_frame_build_code body cap mode = frame_len (length body) /\ (length body <= 1484)%nat.
Proof.
  intros body cap mode H. unfold diginet_frame_build_code in *.
  destruct (negb ((mode =? 0) || (mode =? 1))); [lia|].
  rewrite lib_build_code_eq in *. unfold build_code in *.
  destruct (Z.ltb_spec 1484 (Z.of_nat (length body))); [lia|].
  destruct (system_at body); [lia|].
  destruct (cap <? frame_len (length body)); [lia|]. split; [reflexivity | lia].
Qed.

Lemma length_lib_frame : forall dmac smac send ack retry cmd nc body mode,
  length dmac = 6%nat -> length smac = 6%nat -> mode = 0 \/ mode = 1 ->
  Z.of_nat (length (lib_frame dmac smac send ack retry cmd nc body mode)) = frame_len (length body).
Proof.
  intros. rewrite frame_build_bytes by assumption. apply length_build_frame; assumption.
Qed.

Lemma bc_bound : forall bb cap mode, -10 <= diginet_frame_build_code bb cap mode <= 1514.
Proof.
  intros bb cap mode. unfold diginet_frame_build_code. destruct (negb _); [lia|].
  rewrite lib_build_code_eq. unfold build_code.
  destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia|].
  destruct (system_at bb); [lia|].
  destruct (cap <? frame_len (length bb)); [lia|].
  unfold frame_len. lia.
Qed.

(* what the wide contract leaves at out, in the model's words *)
Lemma bout_eq : forall dmac smac send ack retry cmd nc bb mode oj,
  build_out_w dmac smac send ack retry cmd nc bb mode oj =
  (if 0 <=? diginet_frame_build_code bb (Z.of_nat (length oj)) mode
   then lib_frame dmac smac send ack retry cmd nc bb mode ++
        skipn (Z.to_nat (diginet_frame_build_code bb (Z.of_nat (length oj)) mode)) oj
   else oj).
Proof.
  intros dmac smac send ack retry cmd nc bb mode oj. unfold build_out_w. cbv zeta. rewrite bcw_eq.
  destruct (Z.leb_spec 0 (diginet_frame_build_code bb (Z.of_nat (length oj)) mode)) as [H|H]; [|reflexivity].
  rewrite <- (frame_build_bytes dmac smac send ack retry cmd nc bb mode
                (bc_mode bb (Z.of_nat (length oj)) mode H)).
  reflexivity.
Qed.

(* the two stores the binary makes in the other order than the model (:397 before :113) *)
Lemma infl_swap : forall X v n, Z.of_nat (length X) = 65616 ->
  upd (upd X 1860 (put 4 v)) 3384 (put 8 n) = upd (upd X 3384 (put 8 n)) 1860 (put 4 v).
Proof. intros X v n H. apply upd_upd_comm; rewrite ?length_put; lia. Qed.

(* a store of a register holding a 32-bit field is the model's put of the unsigned field *)
Lemma put4_s32 : forall X k, put 4 (s32_at X k) = put 4 (u_at X k 4).
Proof. intros X k. apply put_cong32. unfold s32_at. apply swrap32_mod. Qed.

Lemma put8_u64 : forall v, put 8 v = put 8 (u64 v).
Proof. intros v. apply put_cong64. unfold u64. rewrite Zmod_mod. reflexivity. Qed.

(* ==== branches ==== *)

Lemma sd_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma sd_lts0 : forall v, -2^63 <= v < 2^63 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv. rewrite bv_lts_zero_r, unsigned_lit_wrap.
  destruct (Z.ltb_spec v 0) as [L|L].
  - apply Z.leb_le.
    replace (v mod 2 ^ 64) with (v + 2 ^ 64);
      [lia | rewrite <- (Z.mod_add v 1 (2 ^ 64)) by lia; rewrite Z.mod_small; lia].
  - apply Z.leb_gt. rewrite Z.mod_small; lia.
Qed.

(* the uint32_t sum the binary writes (lw, add, sw) is the model's u32 of the unsigned sum *)
Lemma hc_val : forall X k nc, u32 (u_at X k 4 + nc) = (s32_at X k + bv_swrap 32 nc) mod 2 ^ 32.
Proof.
  intros X k nc. unfold u32, s32_at.
  rewrite (Zplus_mod (bv_swrap 32 (u_at X k 4)) (bv_swrap 32 nc)), !swrap32_mod, <- Zplus_mod. reflexivity.
Qed.


Lemma hc_store : forall X k nc, put 4 (s32_at X k + bv_swrap 32 nc) = put 4 (u32 (u_at X k 4 + nc)).
Proof.
  intros X k nc. apply put_cong32. rewrite (hc_val X k nc). unfold u32. rewrite Zmod_mod. reflexivity.
Qed.

Lemma mod256_of_mod32 : forall u v, u mod 2 ^ 32 = v mod 2 ^ 32 -> u mod 256 = v mod 256.
Proof.
  intros u v H.
  assert (D : (2 ^ 32 | u - v))
    by (apply Z.mod_divide; [lia|]; rewrite Zminus_mod, H, Z.sub_diag; reflexivity).
  destruct D as [c Hc].
  assert (Hu : u = v + c * 2 ^ 24 * 256)
    by (rewrite <- Z.mul_assoc; change (2 ^ 24 * 256) with (2 ^ 32); lia).
  rewrite Hu. apply Z.mod_add. lia.
Qed.

Lemma b8_cong : forall u v, u mod 256 = v mod 256 -> b8 u = b8 v.
Proof.
  intros u v H. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. exact H.
Qed.

Lemma nc_byte : forall nc, b8 (bv_swrap 32 nc) = b8 (u8 nc).
Proof.
  intros nc. apply b8_cong.
  rewrite (mod256_of_mod32 _ _ (swrap32_mod nc)). unfold u8. rewrite Zmod_mod. reflexivity.
Qed.



(* The kit's cell_of_bytes (Lib/Step.v:527) knows le8 / le4 / le2 and a one-element list, but not the bytes an
   sb of a register writes, [le1 reg]; the store's aftermath would then be skipped and the world lost. One hook
   puts a one-byte store in the list form before the kit's own. *)
Ltac sd_fix1 :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?v))) _) =>
      rewrite (le1_put v); change (put 1 v) with [b8 v]
  | _ => idtac
  end.
Ltac mem_after_store_opt ::= sd_fix1; wk_mem_after_store_opt.

(* side goals of the world algebra: the offsets of g_s's members (OFF_g_s = 1648) and the lengths of the worlds
   the stores make *)
Ltac sd_offs :=
  unfold A_S_host_counter, A_S_cfg_sum_mode, A_S_desk_mac, A_S_cfg_host_mac, A_S_io_send, A_S_inflight,
    A_S_inflight_frame, A_S_inflight_len, A_S_inflight_counter, A_S_inflight_retries, A_S_inflight_sent_us,
    A_S_stats_tx_frames, A_S_stats_tx_data, OFF_g_fail_next, OFF_g_s;
  rewrite ?length_put; cbn [Z.of_nat]; lia.
Ltac sd_len :=
  repeat match goal with
  | |- context [length (upd ?bs ?k (put ?n ?v))] => rewrite (length_upd_put bs k n v); [ | sd_offs | sd_len; sd_offs ]
  | |- context [length (upd ?bs ?k ?v)] => rewrite (length_upd bs v k); [ | sd_offs | sd_len; sd_offs ]
  end.
Ltac sd_side := sd_len; sd_offs.

(* ==== the walk ==== *)

Theorem send_data_holds :
  diginet_frame_build_contract_w -> io_send_contract -> send_data_contract.
Proof.
  intros BUILD IOSEND.
  unfold diginet_frame_build_contract_w, DIGINET_FRAME_BUILD in BUILD.
  unfold io_send_contract, io_send_ENTRY, io_send_FRAME in IOSEND.
  unfold send_data_contract, send_data_ENTRY, send_data_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo bodyp ncmds now r body B B' TF.
  intros A0 A1 A2 A3 A4 NCr NOWr BODY ABLK WM GFN HM SP16 ST LO WOFF MI.
  subst a0 a1 a2 a3 a4.
  unfold arg_blk in ABLK. destruct ABLK as (BP0 & BP64 & BPW & BPS).
  unfold off_world in BPW. unfold off_window in BPS. unfold w_off_stack in WOFF.
  wk_facts.
  assert (Eg : OFF_g_s = 1648) by reflexivity.
  pose proof (wm_len _ _ _ _ WM) as LB.
  assert (ZB : Z.of_nat (length B) = 65616) by (rewrite LB, Z2Nat.id by (unfold W_LEN; lia); reflexivity).
  pose proof (wm_bound _ _ _ _ WM) as WB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as STlo. destruct STlo as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64)
    by (apply unsigned_lit; unfold W_LEN in *; lia).
  pose proof (munch_refl [(bv_unsigned sp - 592, bv_unsigned sp);
                          (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 64%nat ST.
  lazymatch type of FR with
  | rw_cells _ _ ?A [CB _ ?j] =>
      pose proof (rw_cells_split_CB rsegs m A [] 64%nat j [] [8;8;4;2;1;1;8;8;8;8;8]%nat FR eq_refl) as FR2
  end.
  clear FR. rename FR2 into FR. cbn [mk_CB_cells app] in FR.
  do 12 step.
  apply c8_to_cb in FR.
  do 14 step.
  lazymatch goal with
  | H : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) _] |- _ => rename H into WM
  end.
  (* the world now holds the model's :391 store of s->host_counter *)
  rewrite (hc_store B 1808 ncmds) in WM.
  change (upd B 1808 (put 4 (u32 (u_at B 1808 4 + ncmds))))
    with (set_S_host_counter B (u32 (S_host_counter B + ncmds))) in WM.
  remember (set_S_host_counter B (u32 (S_host_counter B + ncmds))) as M1 eqn:EM1.
  pose proof (wm_len _ _ _ _ WM) as LM1.
  assert (ZM1 : Z.of_nat (length M1) = 65616) by (rewrite LM1, Z2Nat.id by (unfold W_LEN; lia); reflexivity).
  (* the arguments of diginet_frame_build (:393) *)
  assert (MODE : s32_at M1 1668 = s32_at B 1668)
    by (rewrite EM1; unfold set_S_host_counter, A_S_host_counter; apply s32_at_upd_out;
        rewrite ?length_put; [lia|lia|lia|rewrite ZB; lia]).
  assert (LDM : length (sub M1 1768 6) = 6%nat) by (apply length_sub; [lia | rewrite ZM1; lia]).
  assert (LSM : length (sub M1 1648 6) = 6%nat) by (apply length_sub; [lia | rewrite ZM1; lia]).
  assert (LOJ : length (sub M1 1864 1514) = 1514%nat) by (apply length_sub; [lia | rewrite ZM1; lia]).
  assert (LOJZ : Z.of_nat (length (sub M1 1864 1514)) = 1514) by (rewrite LOJ; reflexivity).
  assert (DMAC : bytes_at rsegs m1 (W_BASE_PLAIN + OFF_g_s + 120) (sub M1 1768 6))
    by (apply (wm_src rsegs W_BASE_PLAIN m1 M1 1768 6); [exact WM | lia | lia | unfold W_LEN; lia]).
  assert (SMAC : bytes_at rsegs m1 (W_BASE_PLAIN + OFF_g_s) (sub M1 1648 6))
    by (apply (wm_src rsegs W_BASE_PLAIN m1 M1 1648 6); [exact WM | lia | lia | unfold W_LEN; lia]).
  assert (OJC : rw_cells rsegs m1 (W_BASE_PLAIN + OFF_g_s + 216)
                  [CB (length (sub M1 1864 1514)) (sub M1 1864 1514)])
    by (apply (wm_cell rsegs W_BASE_PLAIN m1 M1 1864 1514); [exact WM | lia | lia | unfold W_LEN; lia]).
  (* the struct diginet_header the six stores filled, at sp + 12 = h + 4 *)
  pose proof (proj1 (proj1 FR)) as FWF. cbn [cells_wf cell_wf] in FWF.
  lazymatch type of FR with
  | rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      pose proof (cells_bytes_at rsegs m1 (bv_unsigned sp + -64) [c0;c1] [c2;c3;c4;c5;c6] rest FR
                    ltac:(cbn [cells_wf cell_wf]; tauto)) as HDR
  end.
  cbn [cells_bytes cbytes cells_size csize app] in HDR.
  rewrite !le4_put, le2_put in HDR.
  rewrite (hc_store B 1808 ncmds) in HDR.
  rewrite (nc_byte ncmds) in HDR.
  lazymatch type of HDR with
  | bytes_at _ _ ?a _ => replace a with (bv_unsigned sp + -56 + 4) in HDR by (cbn [Nat.add]; lia)
  end.
  assert (HCM : u32 (u_at B 1808 4 + ncmds) = S_host_counter M1).
  { rewrite EM1. unfold S_host_counter, A_S_host_counter, set_S_host_counter.
    change (OFF_g_s + 160) with 1808. rewrite u_at_upd_put by (rewrite ?ZB; cbn; lia).
    unfold u32. rewrite Zmod_mod. reflexivity. }
  rewrite HCM in HDR.
  replace (Z_to_bv 64 1514) with (Z_to_bv 64 (Z.of_nat (length (sub M1 1864 1514))))
    by (rewrite LOJ; reflexivity).
  step.                                      (* 17134 jal diginet_frame_build *)
  eapply evt_cut.
  { eapply (BUILD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (W_BASE_PLAIN + OFF_g_s + 216) (W_BASE_PLAIN + OFF_g_s + 120) (W_BASE_PLAIN + OFF_g_s)
              (bv_unsigned sp + -56) bodyp (s32_at B 1668) lo (S_host_counter M1) 0 0 0 (u8 ncmds)
              (sub M1 1768 6) (sub M1 1648 6) body (sub M1 1864 1514)).
    - unfold W_LEN in *; lia.
    - unfold W_LEN in *; lia.
    - unfold W_LEN in *; lia.
    - unfold W_LEN in *; lia.
    - left. lia.
    - pose proof (s32_range B 1668). lia.
    - rewrite <- HCM. unfold u32. pose proof (Z.mod_pos_bound (u_at B 1808 4 + ncmds) (2 ^ 32)). lia.
    - lia.
    - lia.
    - lia.
    - unfold u8. pose proof (Z.mod_pos_bound ncmds 256). lia.
    - unfold W_LEN in *; lia.
    - exact LDM.
    - exact DMAC.
    - exact LSM.
    - exact SMAC.
    - exact HDR.
    - exact BODY.
    - exact OJC.
    - rewrite LOJ; unfold W_LEN in *; lia.
    - rewrite LOJ; unfold W_LEN in *; lia.
    - rewrite LOJ; unfold W_LEN in *; lia.
    - rewrite LOJ; unfold W_LEN in *; lia.
    - rewrite Hsp. exact ST.
    - rewrite Hsp. unfold W_LEN in *; lia.
    - rewrite ?LOJ, ?Hsp; unfold W_LEN in *; lia.
    - rewrite ?LOJ, ?Hsp; unfold W_LEN in *; lia.
    - rewrite ?LOJ, ?Hsp; unfold W_LEN in *; lia.
    - rewrite ?LOJ, ?Hsp; unfold W_LEN in *; lia.
    - rewrite ?LOJ, ?Hsp; unfold W_LEN in *; lia.
    - exact MI. }
  wk_post_call rsegs m1.
  lazymatch goal with
  | H : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) _] |- _ => rename H into WM
  end.
  lazymatch goal with | H : stk rsegs _ lo _ |- _ => rename H into ST end.
  lazymatch goal with | H : mem_inv rsegs _ |- _ => rename H into MI end.
  rewrite Hsp in ST.
  assert (ECODE : build_code_w body (Z.of_nat (length (sub M1 1864 1514))) (s32_at B 1668)
                  = diginet_frame_build_code body 1514 (s32_at B 1668))
    by (rewrite LOJ; apply bcw_eq).
  rewrite ECODE.
  rewrite (bout_eq (sub M1 1768 6) (sub M1 1648 6) (S_host_counter M1) 0 0 0 (u8 ncmds) body
             (s32_at B 1668) (sub M1 1864 1514)), LOJZ in WM.
  assert (GFN1 : g_fail_next M1 = g_fail_next B).
  { rewrite EM1. unfold g_fail_next, set_S_host_counter, A_S_host_counter, OFF_g_fail_next.
    apply u_at_upd_out; rewrite ?length_put; [lia|lia|lia|rewrite ZB; lia]. }
  (* the model: :393-396 *)
  unfold send_data_m in HM. cbv zeta in HM. rewrite <- EM1 in HM.
  unfold S_cfg_sum_mode, A_S_cfg_sum_mode, DIGINET_MAX_FRAME_LEN in HM.
  change (OFF_g_s + 0 + 20) with 1668 in HM.
  rewrite MODE in HM.
  do 2 step.                                 (* 17138 mv a2,a0 ; 1713c bltz a0 *)
  rewrite (sd_lts0 (diginet_frame_build_code body 1514 (s32_at B 1668))
             ltac:(pose proof (bc_bound body 1514 (s32_at B 1668)); lia)).
  destruct (Z.ltb_spec (diginet_frame_build_code body 1514 (s32_at B 1668)) 0) as [NEG|POS]; cbv iota.
  - (* :395-396 the build refused: the world keeps only the host-counter store *)
    replace (diginet_frame_build_code body 1514 (s32_at B 1668) <? 0) with true in HM
      by (symmetry; apply Z.ltb_lt; exact NEG).
    cbv beta iota in HM. injection HM as EB' Er. subst B' r.
    replace (0 <=? diginet_frame_build_code body 1514 (s32_at B 1668)) with false in WM
      by (symmetry; apply Z.leb_gt; exact NEG).
    cbv beta iota in WM.
    rewrite upd_sub_id in WM by (rewrite ?ZM1; lia).
    do 6 step.                               (* 1719c mv a0,a2 ; 171a0 .. 171b0 the five ld *)
    release_frame FR ST (bv_unsigned sp).
    do 2 step.                               (* 171b4 addi sp,sp,64 ; 171b8 ret *)
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WMO|]. split; [exact MI|]. split; [exact ST|].
    split; [exact WM | rewrite GFN1; exact GFN].
  - (* :397-400 *)
    replace (diginet_frame_build_code body 1514 (s32_at B 1668) <? 0) with false in HM
      by (symmetry; apply Z.ltb_ge; exact POS).
    cbv beta iota in HM.
    replace (0 <=? diginet_frame_build_code body 1514 (s32_at B 1668)) with true in WM
      by (symmetry; apply Z.leb_le; exact POS).
    cbv beta iota in WM.
    (* the model's frame is the contract's *)
    unfold S_desk_mac, A_S_desk_mac, S_cfg_host_mac, A_S_cfg_host_mac, DIGINET_CMD_DATA in HM.
    change (OFF_g_s + 120) with 1768 in HM. change (OFF_g_s + 0 + 0) with 1648 in HM.
    pose proof (bc_val body 1514 (s32_at B 1668) POS) as (ENN & LBODY).
    pose proof (bc_bound body 1514 (s32_at B 1668)) as NNB.
    remember (lib_frame (sub M1 1768 6) (sub M1 1648 6) (S_host_counter M1) 0 0 0 (u8 ncmds) body
                (s32_at B 1668)) as LF eqn:ELF.
    assert (LFLEN : Z.of_nat (length LF) = diginet_frame_build_code body 1514 (s32_at B 1668)).
    { rewrite ELF, length_lib_frame
        by (first [exact LDM | exact LSM | exact (bc_mode body 1514 (s32_at B 1668) POS)]). lia. }
    assert (LFN : length LF = Z.to_nat (diginet_frame_build_code body 1514 (s32_at B 1668))) by lia.
    rewrite <- LFN in WM.
    rewrite (upd_app_tail M1 LF 1864 1514 ltac:(lia)
               ltac:(rewrite LM1; unfold W_LEN in *; lia) ltac:(lia)) in WM.
    change (upd M1 1864 LF) with (set_S_inflight_frame M1 LF) in WM.
    remember (set_S_inflight_frame M1 LF) as M2 eqn:EM2.
    pose proof (wm_len _ _ _ _ WM) as LM2.
    assert (ZM2 : Z.of_nat (length M2) = 65616) by (rewrite LM2, Z2Nat.id by (unfold W_LEN; lia); reflexivity).
    (* the model: inflight_start (:398, inlined) and stats.tx_data (:399) *)
    unfold inflight_start_m in HM. cbv beta iota zeta in HM.
    set (B3 := set_S_inflight_len M2 (diginet_frame_build_code body 1514 (s32_at B 1668))) in HM.
    set (B7 := set_S_inflight_sent_us (set_S_inflight_retries (set_S_inflight_counter (set_S_inflight B3 1)
                 (S_host_counter B3)) 0) now) in HM.
    set (B8 := set_S_stats_tx_data B7 (u64 (S_stats_tx_data B7 + 1))) in HM.
    (* 17140 lui a0,0x4 ; 17144 lw a1,160(s1) ; 17148 li a3,1 ; 1714c addiw s3,a0,1808 ; 17150 sw a3,212(s1) ;
       17154 add s3,s1,s3 ; 17158 ld a3,8(s3) ; 1715c ld a0,64(s1) ; 17160 ld a4,72(s1) ; 17164 sd a2,1736(s1) ;
       17168 sw a1,1744(s1) ; 1716c sw zero,1748(s1) ; 17170 sd s0,1752(s1) ; 17174 addi a3,a3,1 ;
       17178 sd a3,8(s3) ; 1717c mv a1,s2 *)
    do 16 step.
    (* the world the binary leaves is the model's B8: the two stores of :397 and :113 in the other order, and each
       value modulo the width of its field *)
    assert (EW8 : upd (upd (upd (upd (upd (upd M2 1860 (put 4 1)) 3384
                    (put 8 (diginet_frame_build_code body 1514 (s32_at B 1668))))
                    3392 (put 4 (s32_at M2 1808))) 3396 (put 4 0)) 3400 (put 8 now))
                    19848 (put 8 (u_at (upd M2 1860 (put 4 1)) 19848 8 + 1)) = B8).
    { rewrite (upd_upd_comm M2 (put 4 1) (put 8 (diginet_frame_build_code body 1514 (s32_at B 1668))) 1860 3384)
        by sd_side.
      assert (V1 : put 4 (s32_at M2 1808) = put 4 (S_host_counter B3)).
      { unfold S_host_counter, B3, set_S_inflight_len. rewrite u_at_upd_out by sd_side.
        change A_S_host_counter with 1808. apply put4_s32. }
      assert (ETX : u_at (upd M2 1860 (put 4 1)) 19848 8 = S_stats_tx_data B7).
      { unfold S_stats_tx_data, B7, B3, set_S_inflight_sent_us, set_S_inflight_retries, set_S_inflight_counter,
          set_S_inflight, set_S_inflight_len.
        repeat rewrite u_at_upd_out by sd_side. reflexivity. }
      rewrite V1, ETX.
      unfold B8, B7, B3, set_S_stats_tx_data, set_S_inflight_sent_us, set_S_inflight_retries,
        set_S_inflight_counter, set_S_inflight, set_S_inflight_len.
      unfold u64. rewrite put_mod64 by lia. reflexivity. }
    lazymatch goal with W : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) (upd _ 19848 _)] |- _ =>
      rewrite EW8 in W; rename W into WM8 end.
    pose proof (wm_len _ _ _ _ WM8) as LB8.
    (* the model: the inflight_len bytes of the frame, and the test of s->io.send against io_send *)
    assert (ELEN : S_inflight_len B8 = diginet_frame_build_code body 1514 (s32_at B 1668)).
    { unfold S_inflight_len, B8, B7, B3, set_S_stats_tx_data, set_S_inflight_sent_us, set_S_inflight_retries,
        set_S_inflight_counter, set_S_inflight, set_S_inflight_len.
      repeat rewrite u_at_upd_out by sd_side. rewrite u_at_upd_put by sd_side.
      apply Z.mod_small. change (2 ^ (8 * Z.of_nat 8)) with (2^64). lia. }
    unfold inflight_bytes in HM. rewrite ELEN in HM.
    replace (1514 <? diginet_frame_build_code body 1514 (s32_at B 1668)) with false in HM
      by (symmetry; apply Z.ltb_ge; lia).
    cbv beta iota in HM.
    set (fr := sub B8 A_S_inflight_frame (Z.to_nat (diginet_frame_build_code body 1514 (s32_at B 1668)))) in HM.
    assert (LFR : Z.of_nat (length fr) = diginet_frame_build_code body 1514 (s32_at B 1668))
      by (unfold fr; rewrite length_sub by sd_side; lia).
    unfold send_raw_m, call_send in HM.
    destruct (Z.eqb_spec (S_io_send B8) (ti_io_send timg_plain)) as [HSND|NSND]; cbv beta iota in HM;
      [|discriminate HM].
    destruct (io_send_m timg_plain B8 fr) as [[B9 r0]|] eqn:HIO; cbv beta iota in HM; [|discriminate HM].
    assert (EA4 : u_at (upd M2 1860 (put 4 1)) 1720 8 = 83180).
    { transitivity (S_io_send B8); [| exact HSND].
      unfold S_io_send, B8, B7, B3, set_S_stats_tx_data, set_S_inflight_sent_us, set_S_inflight_retries,
        set_S_inflight_counter, set_S_inflight, set_S_inflight_len.
      repeat rewrite u_at_upd_out by sd_side. reflexivity. }
    assert (GF8 : g_fail_next B8 = g_fail_next B).
    { unfold g_fail_next, B8, B7, B3, set_S_stats_tx_data, set_S_inflight_sent_us, set_S_inflight_retries,
        set_S_inflight_counter, set_S_inflight, set_S_inflight_len.
      repeat rewrite u_at_upd_out by sd_side.
      rewrite EM2. unfold set_S_inflight_frame. rewrite u_at_upd_out by (rewrite ?LFN; sd_offs).
      exact GFN1. }
    rewrite EA4.
    (* 17180 jalr a4: s->io.send (s->io.ctx, s->inflight_frame, s->inflight_len) is the harness's io_send *)
    step.
    replace (Z_to_bv 64 (diginet_frame_build_code body 1514 (s32_at B 1668)))
      with (Z_to_bv 64 (Z.of_nat (length fr))) by (rewrite LFR; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
    eapply evt_cut.
    { eapply IOSEND with (B := B8) (frame := fr) (lo := lo) (r := r0) (B' := B9)
        (p := W_BASE_PLAIN + OFF_g_s + 216);
        [ reflexivity | reflexivity | unfold W_LEN in *; lia
        | apply (wm_src rsegs W_BASE_PLAIN _ B8 A_S_inflight_frame
                   (Z.to_nat (diginet_frame_build_code body 1514 (s32_at B 1668))));
          [exact WM8 | sd_offs | sd_offs | sd_offs]
        | unfold io_send_frame_at, SZ_g_s; right; rewrite LFR; unfold W_LEN in *; lia
        | unfold off_window; rewrite Hsp, LFR; unfold W_LEN in *; lia
        | rewrite GF8; exact GFN
        | rewrite Hsp; Z.div_mod_to_equations; lia
        | rewrite Hsp; exact ST
        | rewrite Hsp; lia
        | unfold w_off_stack; rewrite Hsp; unfold W_LEN in *; lia
        | assumption
        | exact WM8
        | exact HIO ]. }
    wk_post_call rsegs mS.
    lazymatch goal with | H : stk rsegs _ lo _ |- _ => rename H into ST end.
    lazymatch goal with | H : mem_inv rsegs _ |- _ => rename H into MI end.
    rewrite Hsp in ST.
    lazymatch goal with W : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) B9] |- _ => rename W into WM9 end.
    pose proof (wm_len _ _ _ _ WM9) as LB9.
    pose proof (io_send_m_fail_next _ _ _ _ _ HIO LB8) as GF9.
    pose proof (io_send_m_ret _ _ _ _ _ HIO) as R0. unfold EIO in R0.
    (* 17184 mv a2,a0 ; 17188 bnez a0 (send_raw :91) *)
    do 2 step.
    rewrite (sd_eqb0 r0 ltac:(lia)).
    destruct (Z.eqb_spec r0 0) as [Z0|NZ]; cbn [negb]; cbv iota.
    + (* io_send answered 0: stats.tx_frames++ (:91-92) *)
      cbv beta iota in HM. injection HM as EB' Er. subst B' r. subst r0.
      do 4 step.                             (* 1718c li a2,0 ; 17190 ld a0,0(s3) ; 17194 addi ; 17198 sd a0,0(s3) *)
      assert (EWF : upd B9 19840 (put 8 (u_at B9 19840 8 + 1)) =
                    set_S_stats_tx_frames B9 (u64 (S_stats_tx_frames B9 + 1)))
        by (unfold set_S_stats_tx_frames, S_stats_tx_frames, u64; rewrite put_mod64 by lia; reflexivity).
      lazymatch goal with W : rw_cells rsegs _ W_BASE_PLAIN [CB (Z.to_nat W_LEN) (upd B9 19840 _)] |- _ =>
        rewrite EWF in W; rename W into WMF end.
      do 6 step.                             (* 1719c mv a0,a2 ; 171a0 .. 171b0 the five ld *)
      release_frame FR ST (bv_unsigned sp).
      do 2 step.                             (* 171b4 addi sp,sp,64 ; 171b8 ret *)
      apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WMO|]. split; [exact MI|]. split; [exact ST|].
      split; [exact WMF|].
      unfold g_fail_next, set_S_stats_tx_frames. rewrite u_at_upd_out by sd_side.
      unfold g_fail_next in GF9. lia.
    + (* io_send answered -EIO: send_raw returns it (:93) *)
      cbv beta iota in HM. injection HM as EB' Er. subst B' r.
      do 6 step.                             (* 1719c mv a0,a2 ; 171a0 .. 171b0 the five ld *)
      release_frame FR ST (bv_unsigned sp).
      do 2 step.                             (* 171b4 addi sp,sp,64 ; 171b8 ret *)
      apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WMO|]. split; [exact MI|]. split; [exact ST|].
      split; [exact WM9|]. rewrite GF9. lia.
Qed.
