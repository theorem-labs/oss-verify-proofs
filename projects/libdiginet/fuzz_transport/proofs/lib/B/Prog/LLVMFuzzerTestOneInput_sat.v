(* Satisfiability of the cuts of the image-B walk of LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v)
   at the unit's own instance.

   1. The entry cut (lc_entry_sat). The walk starts from lc_base cx, the slot's pre tfib_lib_pre_x (lib/B/YCfn.v) at
      the entry configuration. For every meter MT the closing of this unit accepts (`forall S m, mo_ok MT S m`, the
      hypothesis MT_FREE of lib/B/YD1m.v, YD1p.v, YD1q.v and TransportDriverB.v, the files that instantiate the slot;
      this tree fixes no meter beyond that hypothesis) and every read-only range [RLO, RHI) inside in_ro_tfa (their
      RO_IN), every state that the driver hands to its call of LLVMFuzzerTestOneInput (lib/B/YD1w.v lib_pre and the
      other premises of its lib_site_x, at the `jal` before RA_LLVMF) satisfies the entry cut, at every frame
      position.
      CONDITIONAL: the entry cut is satisfiable exactly as far as lib_pre and those premises are. In this tree lib_pre
      is shown to hold only inside the driver loop's proof, at the call it makes and under that lemma's own premises
      (the assertion of lib_pre at lib/B/YD1r.v:667 inside the driver's calls_loop, which the whole-program proof
      reaches through loop_L_x, lib/B/YD1p.v:78); no closed lemma exhibits a state satisfying it.
   2. The simulation invariant of the loop head is satisfiable at timg_B, closed (lc_agree_sat): InitOk.v
      prologue_ok at a zero world and the empty input.
   3. The saved words, the spill slots, the frame and the frame's shadow lie apart (lc_ranges_apart), so the cuts'
      facts over those four ranges cannot contradict each other; the cuts' other memory facts (the world bytes of
      lc_tw, the input block, the TRANS_RO_RD bytes) lie apart from these by AR (YG0s.v frame_facts, YCbq.v
      frames_bounds), not by this lemma. The cut's shadow maps and spill slots are bytes and words of distinct offsets
      (LLVMFuzzerTestOneInput_st.v lf_shm_byte, lf_spill_nodup, lf_spill_vals).
   The cuts after the entry are reached from it by the segment statements (llvmf_of_segments). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YM02 YP0m YP09 YI00 YI16 YK04 YA0i YA0n
YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YF0m YCeg YD1t YD20 YD1v YD2h YD2f YD1w.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YCfn YD1u.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree InitOk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module IOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.InitOk.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

Section s. Context {rc : YM05.RunCeil}.

(* 1. the entry cut, from the driver's call state as lib_site_x receives it *)
Theorem lc_entry_sat : forall (B : asyms) (MT : ameter_ops) (XL : Z -> Z) (RLO RHI : Z),
  (forall S m, mo_ok MT S m) -> (forall a, RLO <= a < RHI -> in_ro_tfa a) ->
  forall (fx : YK11.FPState) ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n (pl : list byte) (fpos : Z),
  lib_pre B ly S W regs mem md ->
  getr regs 10%bv = w64 p -> getr regs 11%bv = w64 n ->
  ((n = 0 /\ p = A_EMPTY_tfa) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
  n = Z.of_nat (length pl) -> garr8 tfibsegs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  frames S = [] -> st_nev S + EV_LIB <= EV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
  arodata_ok B (aview tfibsegs (w_H W) mem) ->
  FINV ly (w_H W) mem ->
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None -> Namei.fd_names_path (m_fds md) YI16.sink_path = false ->
  Fs.fs_sorted (m_fs md) = true ->
  exists M, lc_base B MT XL RLO RHI (mkLCx fx ly S W regs mem md p n pl M fpos).
Proof.
intros B MT XL RLO RHI MT_FREE RO_IN fx ly S W regs mem md p n pl fpos HPRE R10 R11 Hpn Hlen Hpl Hfr Hev Hlive Hro
  HFI Hfree Hnames Hsorted.
pose proof HPRE as (HAR & Hret & Hra & Hgp & Htp & Hal & [Wlo Whi] & [Tlo Thi] & Elo & Ehi & Hpres & Hs0 & Hqt).
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC. unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
destruct HFI as ((M & HAM) & Henv & Hhead).
exists M. unfold lc_base, tfib_lib_pre_x. cbn [l_regs l_ly l_S l_W l_mem l_md l_p l_n l_pl l_M].
split.
{ split; [exact HAR|]. split; [exact Hret|]. split; [rewrite Hra; cbv; discriminate|]. split; [exact Hgp|].
  split; [exact Htp|].
  split.
  - unfold astk_ok. rewrite Ehi. unfold ly_bot, kHighMemEnd, LLVMF_STK, ASTACK, kStackSpan in *. repeat split; lia.
  - split; [exact Hpres|]. split; [| exact Hqt]. apply achain_low. exact Hs0. }
split; [exact Hra|]. split; [exact R10|]. split; [exact R11|]. split; [exact Hpn|].
split; [exact Hlen|]. split; [exact Hpl|]. split; [exact Hfr|]. split; [exact Hev|]. split; [exact Hlive|].
split.
{ intros a Ha Hno Hne. apply Hro; [| exact Hno | exact Hne]. destruct Ha as [Ha | Ha]; [left; exact Ha | exact (RO_IN a Ha)]. }
split; [exact (conj Henv (conj Hhead Hnames))|].
split; [exact Hfree|]. split; [exact Hsorted|]. split; [exact HAM | apply MT_FREE].
Qed.

(* the entry cut with its configuration: what lc_entry_stmt's segment starts from *)
Corollary lc_entry_cut_sat : forall (B : asyms) (MT : ameter_ops) (XL : Z -> Z) (RLO RHI : Z),
  (forall S m, mo_ok MT S m) -> (forall a, RLO <= a < RHI -> in_ro_tfa a) ->
  forall (fx : YK11.FPState) ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n (pl : list byte),
  lib_pre B ly S W regs mem md ->
  getr regs 10%bv = w64 p -> getr regs 11%bv = w64 n ->
  ((n = 0 /\ p = A_EMPTY_tfa) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
  n = Z.of_nat (length pl) -> garr8 tfibsegs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  frames S = [] -> st_nev S + EV_LIB <= EV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
  arodata_ok B (aview tfibsegs (w_H W) mem) ->
  FINV ly (w_H W) mem ->
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None -> Namei.fd_names_path (m_fds md) YI16.sink_path = false ->
  Fs.fs_sorted (m_fs md) = true ->
  exists M (c : config),
    @tfib_lib_pre_x rc B MT XL RLO RHI regs ly S W mem md p n pl M /\ c = @cfg_at fx tfibsegs A_LLVMF regs mem md.
Proof.
intros B MT XL RLO RHI MT_FREE RO_IN fx ly S W regs mem md p n pl HPRE R10 R11 Hpn Hlen Hpl Hfr Hev Hlive Hro
  HFI Hfree Hnames Hsorted.
destruct (lc_entry_sat B MT XL RLO RHI MT_FREE RO_IN fx ly S W regs mem md p n pl 0 HPRE R10 R11 Hpn Hlen Hpl Hfr Hev
  Hlive Hro HFI Hfree Hnames Hsorted) as (M & HB).
exists M, (@cfg_at fx tfibsegs A_LLVMF regs mem md). split; [exact HB | reflexivity].
Qed.
End s.

(* 2. timg_B satisfies the image facts the simulation takes (Agree.v timg_ok), by computation, and the head's
   invariant agree timg_B 0 holds of some world: InitOk.prologue_ok at the zero world and the empty input. *)
Lemma lc_timg_B_ok : AG.timg_ok timg_B.
Proof.
constructor; cbv [timg_B TI.ti_io_send TI.ti_io_recv TI.ti_io_now TI.ti_notice TI.ti_spec_c24 TI.ti_spec_pc
  TI.ti_personalities]; change (2 ^ 64) with 18446744073709551616; lia.
Qed.

Lemma lc_agree_sat : exists Bw, AG.agree timg_B 0 Bw.
Proof.
destruct (IOK.prologue_ok timg_B (repeat (DSpec.b8 0) (Z.to_nat TW.W_LEN)) (fun _ => 4096) [] lc_timg_B_ok
  (repeat_length _ _) ltac:(vm_compute; reflexivity)) as (B0 & _ & HA & _).
exists B0. exact HA.
Qed.

(* 3. the ranges of the cuts' memory facts lie apart, for every sp0 and F with the five premises below: 1-2 are
   lc_base's (LLVMFuzzerTestOneInput_st.v lc_geom lg_sp0al, lg_stk), 3-4 are lc_core's, 5 is YCbq.v frames_bounds at
   lc_core's AR and frame (lc_geom lg_ar, lg_Fin, lg_Faddr): the saved words [sp0 - 104, sp0) and the spills
   [sp1, sp1 + 216) on the machine stack; the frame [F, F + 256) (its flag word at F + 248) and its 32 shadow bytes,
   both below the stack, and apart from each other. *)
Section r. Context {rc : YM05.RunCeil}.
Lemma lc_ranges_apart : forall sp0 F,
  sp0 mod 16 = 0 -> alloc_ceiling + LLVMF_STK <= sp0 -> 4096 <= F -> F + LF_FBYTES <= alloc_ceiling ->
  (F + LF_FBYTES <= kLowMemEnd \/ kHighMemBeg <= F) ->
  let sp1 := 32 * ((sp0 - LF_FRAME) / 32) in
  sp0 - 336 <= sp1 <= sp0 - LF_FRAME /\ sp1 mod 32 = 0 /\ sp1 + 216 <= sp0 - 104 /\
  F + LF_FBYTES <= sp1 /\ SHADOW_OFF + F / 8 + 32 <= sp1 /\
  (F + LF_FBYTES <= SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 32 <= F).
Proof.
intros sp0 F H16 Hc H4 HF Happ sp1. subst sp1.
pose proof (Z.div_mod (sp0 - LF_FRAME) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (sp0 - LF_FRAME) 32 ltac:(lia)) as M.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16.
pose proof asan_consts as ((CVlo & CVhi) & _ & _ & _ & _).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as F8.
pose proof (Z.mul_div_le F 8 ltac:(lia)) as F8l.
pose proof (Z.div_mod F 8 ltac:(lia)) as F8d.
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as F8m.
unfold LF_FRAME, LF_FBYTES, LLVMF_STK, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *.
assert (Hm : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
{ assert (E : sp0 - 320 = 16 * (sp0 / 16 - 20)) by lia.
  rewrite E. pose proof (Z.mod_pos_bound (16 * (sp0 / 16 - 20)) 32 ltac:(lia)).
  destruct (Z.even (sp0 / 16 - 20)) eqn:Ev.
  - apply Z.even_spec in Ev. destruct Ev as (h & Eh). rewrite Eh. left.
    replace (16 * (2 * h)) with (h * 32) by lia. apply Z.mod_mul. lia.
  - right. assert (Od : Z.odd (sp0 / 16 - 20) = true) by (rewrite <- Z.negb_even, Ev; reflexivity).
    apply Z.odd_spec in Od. destruct Od as (h & Eh). rewrite Eh.
    replace (16 * (2 * h + 1)) with (16 + h * 32) by lia. rewrite Z.mod_add by lia. reflexivity. }
split; [lia|]. split.
{ rewrite Z.mul_comm. apply Z.mod_mul. lia. }
split; [lia|]. split; [lia|]. split; [lia|].
destruct Happ as [Hlo | Hhi]; [left; lia | right; lia].
Qed.
End r.
