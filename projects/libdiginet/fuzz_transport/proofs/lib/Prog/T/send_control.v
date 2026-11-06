(* Walk of send_control (transport/src/diginet_session.c:97-109) in the plain image: 0x16480, 216 bytes, own frame
   128, send_raw inlined. It builds the 60-byte control frame f[60] on the stack (header h at sp + 12, f at sp + 28)
   with diginet_frame_build (body NULL, length 0: the wide contract), copies it to keep and stores 60 in *keep_len
   when keep is not NULL (memcpy), and sends it through s->io.send (io_send), counting stats.tx_frames on 0.
   The model's Some (send_control_m, TModel/TSess.v) gives the branches: the sum mode decides the build's code
   (-1 for a mode other than 0 and 1: return it), call_send's test gives s->io.send = io_send, and io_send_m's
   Some gives its call. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldLemmas TWorldMem TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TIoSendFail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_build_c diginet_frame_build_w_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import io_send_c send_control_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- bytes and cells ---- *)

(* a byte store of a register Z_to_bv 64 z: the kit's store aftermath (Lib/Step.v cell_of_bytes, its le1 case)
   writes the cell C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))); its byte is b8 z *)
Lemma sc_b8 : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = b8 z.
Proof.
  intros z. unfold b8. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. apply mod_mod8_of_modw. lia.
Qed.

Ltac sb_fix := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => rewrite (sc_b8 z) in H end.

(* the four bytes sw stores of a register holding a 32-bit value sign-extended (lw, or the LP64 ABI) *)
Lemma sc_l4s : forall u, le4 (Z_to_bv 64 (bv_swrap 32 u)) = Z_to_le_bytes 4 u.
Proof.
  intros u. unfold le4. rewrite unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 u) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 u 32) by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma sc_l4s32 : forall B k, le4 (Z_to_bv 64 (s32_at B k)) = Z_to_le_bytes 4 (u_at B k 4).
Proof. intros B k. apply sc_l4s. Qed.

Lemma sc_cb_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma sc_c8 : forall m A v, rw_cells rsegs m A [C8 v] -> rw_cells rsegs m A [CB 8 (le8 v)].
Proof.
  intros m A v H. pose proof (rw_cells_merge rsegs m A [] [C8 v] [] H) as H'.
  cbn [app cells_size cells_bytes cbytes csize Nat.add] in H'. rewrite app_nil_r in H'. exact H'.
Qed.

(* memcpy wrote the cell [p, p + n): the stack [lo, hi) keeps its bytes readable wherever p lies *)
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

(* ---- the model ---- *)

Lemma sc_len_lib_frame : forall d s send ack retry cmd ncmds mode, length d = 6%nat -> length s = 6%nat ->
  length (lib_frame d s send ack retry cmd ncmds [] mode) = 60%nat.
Proof. intros d s send ack retry cmd ncmds mode Hd Hs. unfold lib_frame. rewrite !length_app, repeat_length, Hd, Hs. reflexivity. Qed.

(* the 60 bytes diginet_frame_build leaves in the stack buffer are the model's frame *)
Lemma sc_build_out : forall d s send ack cmd mode oj, mode = 0 \/ mode = 1 -> length oj = 60%nat ->
  build_out_w d s send ack 0 cmd 0 [] mode oj = lib_frame d s send ack 0 cmd 0 [] mode.
Proof.
  intros d s send ack cmd mode oj Hm Ho. unfold build_out_w. rewrite Ho. cbv zeta.
  assert (E : build_code_w [] (Z.of_nat 60) mode = 60) by (unfold build_code_w; destruct Hm as [-> | ->]; reflexivity).
  rewrite E. destruct (Z.leb_spec 0 60) as [_|L]; [|lia].
  rewrite skipn_all2 by (rewrite Ho; cbn; lia). rewrite app_nil_r.
  symmetry. apply frame_build_bytes. exact Hm.
Qed.

Lemma sc_mnn : forall (l d : list byte), length l = 60%nat -> match l with [] => d | _ :: _ => l end = l.
Proof. intros l d H. destruct l; [discriminate H | reflexivity]. Qed.

Lemma sc_mnn2 : forall (l d e : list byte), length l = 60%nat -> match l with [] => d | _ :: _ => e end = e.
Proof. intros l d e H. destruct l; [discriminate H | reflexivity]. Qed.

Lemma sc_gf_tx : forall B v, length B = Z.to_nat W_LEN -> g_fail_next (set_S_stats_tx_frames B v) = g_fail_next B.
Proof.
  intros B v L. unfold set_S_stats_tx_frames, g_fail_next.
  apply u_at_upd_out; unfold A_S_stats_tx_frames, OFF_g_fail_next, OFF_g_s; rewrite ?length_put, ?L; unfold W_LEN; lia.
Qed.

(* ---- walk tactics ---- *)

(* the callee's footprint and wmono about the memory of the goal: carry every fact across the call *)
Ltac sc_transport :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
    match goal with MUc : munch _ ?ma mb, WMc : wmono _ ?ma mb |- _ =>
      transport_after_call rsegs ma mb MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv rsegs ma |- _ => clear H end; try clear ma
    end
  end.

Ltac sc_carve n := match goal with S : stk _ _ _ _ |- _ => carve_frame n S end.
Ltac sc_rel A hi := match goal with S : stk _ _ _ _, Fc : rw_cells _ _ A _ |- _ => release_frame Fc S hi end.

(* 0x16538-0x16554: a0 = s3, the saved registers back, the frame released, ret *)
Ltac sc_epilogue sp :=
  do 6 step;
  sc_rel (bv_unsigned sp + -128) (bv_unsigned sp + -116);
  sc_rel (bv_unsigned sp + -116) (bv_unsigned sp + -100);
  sc_rel (bv_unsigned sp + -100) (bv_unsigned sp + -40);
  sc_rel (bv_unsigned sp + -40) (bv_unsigned sp);
  do 2 step.

Theorem send_control_holds :
  diginet_frame_build_contract_w -> io_send_contract -> memcpy_contract -> send_control_contract.
Proof.
  intros FB IOS MC.
  unfold diginet_frame_build_contract_w, DIGINET_FRAME_BUILD in FB.
  unfold io_send_contract, io_send_ENTRY, io_send_FRAME in IOS.
  unfold memcpy_contract in MC.
  unfold send_control_contract, send_control_ENTRY, send_control_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    cmd ack kp klp r K KL f B B' TF HA0 HA1 HA2 HA3 HA4 Hcmd Hack KP WM GF HM SP16 ST LO WO MI.
  subst a0 a1 a2 a3 a4.
  unfold w_off_stack in WO.
  wk_facts.
  assert (EO : OFF_g_s = 1648) by reflexivity.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
  assert (LB : Z.of_nat (length B) = W_LEN) by (rewrite (wm_len _ _ _ _ WM); lia).
  pose proof (s32_range B A_S_cfg_sum_mode) as RMo. change (s32_at B A_S_cfg_sum_mode) with (S_cfg_sum_mode B) in RMo.
  pose proof (u_at_range B A_S_host_counter 4) as RHC.
  change (u_at B A_S_host_counter 4) with (S_host_counter B) in RHC. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RHC.
  assert (LDM : length (S_desk_mac B) = 6%nat) by (unfold S_desk_mac; apply length_sub; unfold A_S_desk_mac; lia).
  assert (LHM : length (S_cfg_host_mac B) = 6%nat) by (unfold S_cfg_host_mac; apply length_sub; unfold A_S_cfg_host_mac; lia).
  unfold send_control_m in HM. cbv zeta in HM.
  set (fr := lib_frame (S_desk_mac B) (S_cfg_host_mac B) (S_host_counter B) ack 0 cmd 0 [] (S_cfg_sum_mode B)) in HM.
  assert (Lfr : length fr = 60%nat) by (apply sc_len_lib_frame; assumption).
  (* keep = NULL (close :154, on_data :242), or wake's e2 / e2_len (:134-136) *)
  destruct KP as [KP0 | (KC & KA & KLC & KLA & KLM & KS)];
    [ subst kp;
      pose proof (munch_refl [(bv_unsigned sp - 656, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU
    | unfold arg_blk, off_world, off_window, blk_sep in KA, KLA, KS;
      destruct KA as (KA1 & KA2 & KA3 & KA4); destruct KLA as (KL1 & KL2 & KL3 & KL4);
      assert (U : bv_unsigned (Z_to_bv 64 kp) = kp) by (apply unsigned_lit; lia);
      pose proof (munch_refl [(bv_unsigned sp - 656, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN);
                              (kp, kp + 60); (klp, klp + 8)] m) as MU ].
  all: pose proof (wmono_refl rsegs m) as WMO.
  all: lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* the frame: saved registers [sp-40, sp), f[60] [sp-100, sp-40), h [sp-116, sp-100), the rest [sp-128, sp-116) *)
  all: sc_carve 40%nat. all: rename FR into FRs.
  all: sc_carve 60%nat. all: rename FR into FRo.
  all: lazymatch type of FRo with rw_cells _ _ _ [CB _ ?j] => rename j into OJ end.
  all: sc_carve 16%nat. all: rename FR into FRh.
  all: sc_carve 12%nat. all: rename FR into FRl.
  all: assert (Lj : length OJ = 60%nat) by (destruct FRo as [[[Lj _] _] _]; exact Lj).
  (* addi sp; sd ra, s0-s3; mv s1,a4; mv s2,a3; mv s0,a0; lw a0,160(a0) = s->host_counter *)
  all: do 10 step.
  (* sb a1,26(sp): h.cmd; sb zero,27(sp): h.num_commands *)
  all: step. all: sb_fix.
  all: step. all: sb_fix.
  (* lw a7,20(s0) = s->cfg.sum_mode; the rest of h; the arguments; jal diginet_frame_build *)
  all: do 13 step.
  all: change (s32_at B 1668) with (S_cfg_sum_mode B).
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HB : bytes_at rsegs mm (bv_unsigned sp + -116 + 4)
                     (Z_to_le_bytes 4 (S_host_counter B) ++ Z_to_le_bytes 4 ack ++ Z_to_le_bytes 2 0 ++ [b8 cmd; b8 0]))
        by (pose proof FRh as [[_ HB0] _]; cbn [cells_bytes cbytes app] in HB0;
            apply bytes_at_app in HB0; destruct HB0 as [_ HB0]; rewrite length_le4 in HB0;
            change (Z.of_nat 4) with 4 in HB0; rewrite sc_l4s32, sc_l4s in HB0;
            eapply bytes_at_ext; [exact HB0 | reflexivity])
    end.
  all: replace (Z_to_bv 64 60) with (Z_to_bv 64 (Z.of_nat (length OJ))) by (rewrite Lj; reflexivity).
  all: rewrite <- Lj in FRo.
  all: eapply evt_cut;
    [ eapply FB with (lo := lo) (send := S_host_counter B) (ack := ack) (retry := 0) (cmd := cmd) (ncmds := 0)
        (dmac := S_desk_mac B) (smac := S_cfg_host_mac B) (bb := []) (oj := OJ) (mode := S_cfg_sum_mode B)
        (out := bv_unsigned sp + -100) (dst := W_BASE_PLAIN + OFF_g_s + 120) (src := W_BASE_PLAIN + OFF_g_s)
        (hp := bv_unsigned sp + -116) (body := 0);
      [ lia | lia | lia | lia | right; reflexivity | lia | lia | lia | lia | lia | lia | lia
      | exact LDM
      | unfold S_desk_mac; eapply wm_src; [exact WM | unfold A_S_desk_mac; lia | unfold A_S_desk_mac; lia
                                         | unfold A_S_desk_mac; lia]
      | exact LHM
      | unfold S_cfg_host_mac; eapply wm_src; [exact WM | unfold A_S_cfg_host_mac; lia | unfold A_S_cfg_host_mac; lia
                                             | unfold A_S_cfg_host_mac; lia]
      | exact HB
      | apply bytes_at_nil; lia
      | exact FRo
      | lia | lia | lia | cbn [length Z.of_nat]; lia
      | rewrite Hsp; exact ST
      | rewrite Hsp; lia | rewrite Hsp; lia | rewrite Hsp; lia | rewrite Hsp; lia | rewrite Hsp; lia
      | cbn [length Z.of_nat]; rewrite Hsp; lia
      | assumption ]
    | ].
  all: intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m1 &
                   Eq & MUc & WMc & MI1 & ST1 & FRo1).
  all: subst ms'. all: rewrite Hsp in MUc, ST1. all: clear HB.
  all: sc_transport.
  all: rename ST1 into ST.
  all: rewrite (ret_pc_even 0x164e4) by (first [lia | reflexivity]).
  all: rewrite Lj in FRo1 |- *. all: change (Z.of_nat 60) with 60.
  (* goals: keep = NULL, then keep = wake's e2 *)
  - (* the build's code: 60 for sum mode 0 or 1, else -1 (DIGINET_E_ARG) *)
    destruct ((S_cfg_sum_mode B =? 0) || (S_cfg_sum_mode B =? 1)) eqn:EM.
    + (* mode 0 or 1: the frame is built and sent *)
      assert (HM01 : S_cfg_sum_mode B = 0 \/ S_cfg_sum_mode B = 1)
        by (apply orb_true_iff in EM; destruct EM as [E|E]; apply Z.eqb_eq in E; [left|right]; exact E).
      assert (EC : build_code_w [] 60 (S_cfg_sum_mode B) = 60) by (unfold build_code_w; rewrite EM; reflexivity).
      assert (EN : diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN (S_cfg_sum_mode B) = 60)
        by (unfold diginet_frame_build_code; rewrite EM; reflexivity).
      rewrite EC.
      rewrite (sc_build_out _ _ _ _ _ _ OJ HM01 Lj) in FRo1. fold fr in FRo1.
      rewrite EN in HM. replace (60 <? 0) with false in HM by reflexivity. cbv beta iota in HM.
      unfold send_raw_m, call_send in HM.
      destruct (S_io_send B =? ti_io_send timg_plain) eqn:ESend; [|discriminate HM].
      destruct (io_send_m timg_plain B fr) as [[B1 r1]|] eqn:HIO; [|discriminate HM].
      cbv beta iota in HM.
      apply Z.eqb_eq in ESend. change (ti_io_send timg_plain) with 0x144ec in ESend.
      (* mv s3,a0; bltz a0 not taken; beqz s2 taken (keep = NULL) *)
      step. step. if_false. step. if_true.
      (* ld a0,64(s0); ld a3,72(s0): a3 = s->io.send, io_send *)
      do 2 step.
      change (u_at B 1720 8) with (S_io_send B). rewrite ESend.
      (* addi a1,sp,28; mv a2,s3; jalr a3 *)
      do 3 step.
      eapply evt_cut.
      { eapply IOS with (lo := lo) (B := B) (B' := B1) (r := r1) (frame := fr) (p := bv_unsigned sp + -100);
          [ reflexivity | rewrite Lfr; reflexivity | lia | eapply sc_cb_bytes; exact FRo1
          | unfold io_send_frame_at; left; unfold off_world; rewrite Lfr; lia
          | unfold off_window; rewrite Hsp; right; lia
          | exact GF | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
          | unfold w_off_stack; rewrite Hsp; lia | assumption | exact WM | exact HIO ]. }
      intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 &
                  Eq & MUc & WMc & MI3 & ST3 & WM3).
      subst ms'. rewrite Hsp in MUc, ST3.
      pose proof (io_send_m_fail_next _ _ _ _ _ HIO (wm_len _ _ _ _ WM)) as GF1.
      pose proof (wm_len _ _ _ _ WM3) as LB1.
      clear WM. sc_transport. rename ST3 into ST. rename WM3 into WM.
      rewrite (ret_pc_even 0x16518) by (first [lia | reflexivity]).
      destruct (io_send_m_ret _ _ _ _ _ HIO) as [R | R]; subst r1.
      * (* io_send answered 0: mv s3,a0; bnez a0 not taken; li s3,0; s->stats.tx_frames++ *)
        replace (0 =? 0) with true in HM by reflexivity. cbv beta iota in HM. injection HM as <- <- <-.
        step. step. if_false.
        do 6 step.
        sc_epilogue sp.
        apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WMO|]. split; [assumption|]. split; [exact ST|].
        replace (set_S_stats_tx_frames B1 (u64 (S_stats_tx_frames B1 + 1)))
          with (upd B1 19840 (put 8 (u_at B1 19840 8 + 1)))
          by (unfold set_S_stats_tx_frames, S_stats_tx_frames, u64; rewrite put_mod64 by lia; reflexivity).
        split; [eassumption|].
        split; [change (upd B1 19840 (put 8 (u_at B1 19840 8 + 1)))
                  with (set_S_stats_tx_frames B1 (u_at B1 19840 8 + 1));
                rewrite sc_gf_tx by exact LB1; lia|].
        left; reflexivity.
      * (* io_send answered -EIO: mv s3,a0; bnez a0 taken; return it *)
        replace (- EIO =? 0) with false in HM by reflexivity. cbv beta iota in HM. injection HM as <- <- <-.
        change (- EIO) with (-5).
        step. step. if_true.
        sc_epilogue sp.
        apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WMO|]. split; [assumption|]. split; [exact ST|].
        split; [exact WM|]. split; [lia|]. left; reflexivity.
    + (* another mode: mv s3,a0; bltz a0 taken; return the build's -1 *)
      assert (EC : build_code_w [] 60 (S_cfg_sum_mode B) = -1) by (unfold build_code_w; rewrite EM; reflexivity).
      assert (EN : diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN (S_cfg_sum_mode B) = -1)
        by (unfold diginet_frame_build_code; rewrite EM; reflexivity).
      rewrite EC.
      rewrite EN in HM. replace (-1 <? 0) with true in HM by reflexivity. cbv beta iota in HM.
      injection HM as <- <- <-.
      step. step. if_true.
      sc_epilogue sp.
      apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WMO|]. split; [assumption|]. split; [exact ST|].
      split; [exact WM|]. split; [exact GF|]. left; reflexivity.
  - assert (Ekp : (kp =? 0) = false) by (apply Z.eqb_neq; lia).
    destruct ((S_cfg_sum_mode B =? 0) || (S_cfg_sum_mode B =? 1)) eqn:EM.
    + (* mode 0 or 1: the frame is built, kept and sent *)
      assert (HM01 : S_cfg_sum_mode B = 0 \/ S_cfg_sum_mode B = 1)
        by (apply orb_true_iff in EM; destruct EM as [E|E]; apply Z.eqb_eq in E; [left|right]; exact E).
      assert (EC : build_code_w [] 60 (S_cfg_sum_mode B) = 60) by (unfold build_code_w; rewrite EM; reflexivity).
      assert (EN : diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN (S_cfg_sum_mode B) = 60)
        by (unfold diginet_frame_build_code; rewrite EM; reflexivity).
      rewrite EC.
      rewrite (sc_build_out _ _ _ _ _ _ OJ HM01 Lj) in FRo1. fold fr in FRo1.
      rewrite EN in HM. replace (60 <? 0) with false in HM by reflexivity. cbv beta iota in HM.
      unfold send_raw_m, call_send in HM.
      destruct (S_io_send B =? ti_io_send timg_plain) eqn:ESend; [|discriminate HM].
      destruct (io_send_m timg_plain B fr) as [[B1 r1]|] eqn:HIO; [|discriminate HM].
      cbv beta iota in HM.
      apply Z.eqb_eq in ESend. change (ti_io_send timg_plain) with 0x144ec in ESend.
      (* mv s3,a0; bltz a0 not taken; beqz s2 not taken *)
      step. step. if_false. step. if_false.
      (* addi a1,sp,28; mv a0,s2; mv a2,s3; jal memcpy (keep, f, n) *)
      do 4 step.
      eapply evt_cut.
      { eapply MC with (src := fr) (junk := K);
          [ rewrite (unsigned_lit (bv_unsigned sp + -100)) by lia; eapply sc_cb_bytes; exact FRo1
          | rewrite Lfr; reflexivity
          | rewrite U; exact KC
          | rewrite U, (unsigned_lit (bv_unsigned sp + -100)) by lia; change (bv_unsigned (Z_to_bv 64 60)) with 60; lia
          | assumption ]. }
      intros ms' PO. unfold memcpy_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 &
                      Eq & MUc & WMc & MI2 & KC2 & BS2).
      subst ms'. clear BS2.
      rewrite U in MUc, KC2.
      change (bv_unsigned (Z_to_bv 64 60)) with 60 in MUc, KC2. change (Z.to_nat 60) with 60%nat in KC2.
      assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -128))
        by (eapply sc_stk_cell with (n := 60%nat); [exact ST | exact MUc | exact WMc | exact KC2]).
      clear KC. sc_transport. try clear ST. rename ST2 into ST.
      rewrite (ret_pc_even 0x16500) by (first [lia | reflexivity]).
      (* sd s3,0(s1): *keep_len = n *)
      step.
      (* ld a0,64(s0); ld a3,72(s0): a3 = s->io.send, io_send *)
      do 2 step.
      change (u_at B 1720 8) with (S_io_send B). rewrite ESend.
      (* addi a1,sp,28; mv a2,s3; jalr a3 *)
      do 3 step.
      eapply evt_cut.
      { eapply IOS with (lo := lo) (B := B) (B' := B1) (r := r1) (frame := fr) (p := bv_unsigned sp + -100);
          [ reflexivity | rewrite Lfr; reflexivity | lia | eapply sc_cb_bytes; exact FRo1
          | unfold io_send_frame_at; left; unfold off_world; rewrite Lfr; lia
          | unfold off_window; rewrite Hsp; right; lia
          | exact GF | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
          | unfold w_off_stack; rewrite Hsp; lia | assumption | exact WM | exact HIO ]. }
      intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 &
                  Eq & MUc & WMc & MI3 & ST3 & WM3).
      subst ms'. rewrite Hsp in MUc, ST3.
      pose proof (io_send_m_fail_next _ _ _ _ _ HIO (wm_len _ _ _ _ WM)) as GF1.
      pose proof (wm_len _ _ _ _ WM3) as LB1.
      clear WM. sc_transport. rename ST3 into ST. rename WM3 into WM.
      rewrite (ret_pc_even 0x16518) by (first [lia | reflexivity]).
      apply sc_c8 in KLC. rewrite le8_put in KLC.
      destruct (io_send_m_ret _ _ _ _ _ HIO) as [R | R]; subst r1.
      * (* io_send answered 0: mv s3,a0; bnez a0 not taken; li s3,0; s->stats.tx_frames++ *)
        replace (0 =? 0) with true in HM by reflexivity. cbv beta iota in HM. injection HM as <- <- <-.
        step. step. if_false.
        do 6 step.
        sc_epilogue sp.
        apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
        rewrite Ekp.
        split; [exact MU|]. split; [exact WMO|]. split; [assumption|]. split; [exact ST|].
        replace (set_S_stats_tx_frames B1 (u64 (S_stats_tx_frames B1 + 1)))
          with (upd B1 19840 (put 8 (u_at B1 19840 8 + 1)))
          by (unfold set_S_stats_tx_frames, S_stats_tx_frames, u64; rewrite put_mod64 by lia; reflexivity).
        split; [eassumption|].
        split; [change (upd B1 19840 (put 8 (u_at B1 19840 8 + 1)))
                  with (set_S_stats_tx_frames B1 (u_at B1 19840 8 + 1));
                rewrite sc_gf_tx by exact LB1; lia|].
        right. rewrite (sc_mnn fr K Lfr), (sc_mnn2 fr KL _ Lfr), Lfr. split; [exact KC2 | exact KLC].
      * (* io_send answered -EIO: mv s3,a0; bnez a0 taken; return it *)
        replace (- EIO =? 0) with false in HM by reflexivity. cbv beta iota in HM. injection HM as <- <- <-.
        change (- EIO) with (-5).
        step. step. if_true.
        sc_epilogue sp.
        apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
        rewrite Ekp.
        split; [exact MU|]. split; [exact WMO|]. split; [assumption|]. split; [exact ST|].
        split; [exact WM|]. split; [lia|].
        right. rewrite (sc_mnn fr K Lfr), (sc_mnn2 fr KL _ Lfr), Lfr. split; [exact KC2 | exact KLC].
    + (* another mode: mv s3,a0; bltz a0 taken; return the build's -1; keep untouched *)
      assert (EC : build_code_w [] 60 (S_cfg_sum_mode B) = -1) by (unfold build_code_w; rewrite EM; reflexivity).
      assert (EN : diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN (S_cfg_sum_mode B) = -1)
        by (unfold diginet_frame_build_code; rewrite EM; reflexivity).
      rewrite EC.
      rewrite EN in HM. replace (-1 <? 0) with true in HM by reflexivity. cbv beta iota in HM.
      injection HM as <- <- <-.
      step. step. if_true.
      sc_epilogue sp.
      apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
      rewrite Ekp.
      split; [exact MU|]. split; [exact WMO|]. split; [assumption|]. split; [exact ST|].
      split; [exact WM|]. split; [exact GF|].
      right. split; [exact KC | exact KLC].
Qed.
