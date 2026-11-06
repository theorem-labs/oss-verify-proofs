(* Satisfiability of the boundary layer of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v)
   at the unit's own instance.

   1. The entry state (bmain_entry_sat). The walk's statements start from `inv_entry g W c /\ e_pre g`. At image B's
      own symbols TfibB (lib/AU/YD2l.v) and sink tfib_K (lib/AU/YE2k.v), for every meter MT the B harness form
      accepts (`forall S m, mo_ok MT S m`, the hypothesis MT_FREE of lib/AU/YD1m.v and YD1p.v), every state that the
      B start-up chain hands to the harness's call of LLVMFuzzerTestOneInput (the predicate lib_pre of lib/AU/YD1w.v
      and the other premises of its lib_site_x, at the `jal` before RA_LLVMF) satisfies the entry cut and e_pre.
      bmain_entry_sat_triv is the same at ameter_triv, the meter the released tops of this route instantiate.
      CONDITIONAL: the entry cut is satisfiable exactly as far as lib_pre and its premises are. In this tree lib_pre
      is shown to hold only inside the driver loop's proof, at every call it makes and under that lemma's own
      premises (lib/AU/YD1r.v calls_loop, the assertion PRE); no closed lemma exhibits a state satisfying it.
   2. The machine-stack, frame and shadow ranges every cut's memory facts are stated over lie apart
      (bmain_ranges_apart), so those facts cannot contradict each other.
   3. The record and shadow-map parts of the cuts: codec_bmain_inv.v's bmain_pure_sat.
   The cuts after the entry are reached from it by the segment statements (bmain_of_segments). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YM02 YP0m YP09 YI00 YI16 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YE00 YE01 YCbq YCbp YC5d YO09 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU codec_bmain_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YE2k YD1u YD1w YD2l YD2f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* 1. the entry state, from the harness's call state as lib_site_x receives it *)
Theorem bmain_entry_sat : forall (MT : ameter_ops) (XM_LIB : Z -> Z),
  (forall S m, mo_ok MT S m) ->
  forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n (pl : list byte),
  lib_pre TfibB ly S W regs mem md ->
  getr regs 10%bv = w64 p -> getr regs 11%bv = w64 n ->
  ((n = 0 /\ p = YD2f.A_EMPTY_tfa) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks TfibB ly S))) ->
  n = Z.of_nat (length pl) -> garr8 tfibsegs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  frames S = [] -> st_nev S + YCfl.EV_LIB <= EV_MAX -> blocks_bytes S + YCfl.LIVE_LIB <= LIVE_MAX ->
  YCeg.arodata_ok TfibB (aview tfibsegs (w_H W) mem) ->
  FINV ly (w_H W) mem ->
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None -> Namei.fd_names_path (m_fds md) YI16.sink_path = false ->
  Fs.fs_sorted (m_fs md) = true ->
  exists M c, inv_entry (mkEctx ly S W mem md regs p n pl M) W c /\
              e_pre TfibB MT tfib_K XM_LIB (mkEctx ly S W mem md regs p n pl M).
Proof.
intros MT XM_LIB MT_FREE ly S W regs mem md p n pl HPRE R10 R11 Hpn Hlen Hpl Hfr Hev Hlive Hro HFI Hfree Hnames Hsorted.
pose proof HPRE as (HAR & Hret & Hra & Hgp & Htp & Hal & [Wlo Whi] & [Tlo Thi] & Elo & Ehi & Hpres & Hs0 & Hqt).
pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC. unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
destruct HFI as ((M & HAM) & Henv & Hhead).
exists M, (cfg_at tfibsegs YCfm.A_LLVMF regs mem md). split; [split; reflexivity|].
unfold e_pre, codec_lib_pre_x. cbn [e_regs e_ly e_S e_W e_mem e_md e_p e_n e_pl e_M].
split.
{ split; [exact HAR|]. split; [exact Hret|]. split; [rewrite Hra; cbv; discriminate|]. split; [exact Hgp|]. split; [exact Htp|].
  split.
  - unfold astk_ok. rewrite Ehi. unfold ly_bot, kHighMemEnd, YCfm.LLVMF_STK, YCfl.LLVMF_STK, ASTACK, kStackSpan in *.
    repeat split; lia.
  - split; [exact Hpres|]. split; [| exact Hqt]. apply achain_low. exact Hs0. }
split; [exact Hra|]. split; [exact R10|]. split; [exact R11|]. split; [exact Hpn|].
split; [exact Hlen|]. split; [exact Hpl|]. split; [exact Hfr|].
split; [unfold YCfm.EV_LIB, YCfl.EV_LIB in *; lia|]. split; [exact Hlive|].
split.
{ intros a Ha Hno Hne. apply Hro; [| exact Hno | exact Hne].
  destruct Ha as [Ha | Ha]; [left; exact Ha | right; unfold CB_RLO, CB_RHI in Ha; exact Ha]. }
split; [exact (conj Henv (conj Hhead Hnames))|].
split; [exact Hfree|]. split; [exact Hsorted|]. split; [exact HAM | apply MT_FREE].
Qed.

(* the same at ameter_triv: the meter of libreac/fuzz_knock's closing (lib/A/AD2o.v) and reac-pw/fuzz_qdisc's
   (lib/AU/APgLib.v qdisc_lib_x_all), the tops of this route, and the one codec's B top takes through MT_FREE *)
Corollary bmain_entry_sat_triv : forall (XM_LIB : Z -> Z) ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n
  (pl : list byte),
  lib_pre TfibB ly S W regs mem md ->
  getr regs 10%bv = w64 p -> getr regs 11%bv = w64 n ->
  ((n = 0 /\ p = YD2f.A_EMPTY_tfa) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks TfibB ly S))) ->
  n = Z.of_nat (length pl) -> garr8 tfibsegs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  frames S = [] -> st_nev S + YCfl.EV_LIB <= EV_MAX -> blocks_bytes S + YCfl.LIVE_LIB <= LIVE_MAX ->
  YCeg.arodata_ok TfibB (aview tfibsegs (w_H W) mem) ->
  FINV ly (w_H W) mem ->
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None -> Namei.fd_names_path (m_fds md) YI16.sink_path = false ->
  Fs.fs_sorted (m_fs md) = true ->
  exists M c, inv_entry (mkEctx ly S W mem md regs p n pl M) W c /\
              e_pre TfibB ameter_triv tfib_K XM_LIB (mkEctx ly S W mem md regs p n pl M).
Proof. intros XM_LIB. apply (bmain_entry_sat ameter_triv XM_LIB). intros S m. exact I. Qed.

(* 2. the ranges of the cuts' memory facts lie apart, for every entry sp0 and frame F the journal allows: the spills
   [sp1 + 16, sp1 + 160), the cursor [sp1 + 184, sp1 + 200), OWE10's scratch [sp1 + 206, sp1 + 216) and the saved
   words [sp0 - 104, sp0) on the machine stack; the frame [F, F + 512) (the flag word at F + 504 inside it) and its
   64 shadow bytes, both below the stack. *)
Lemma bmain_ranges_apart : forall sp0 F,
  sp0 mod 16 = 0 -> alloc_ceiling + 32768 <= sp0 -> 4096 <= F -> F + 512 <= alloc_ceiling ->
  (F + 512 <= 0x7fff8000 \/ 0x10007fff8000 <= F) ->
  let sp1 := 32 * ((sp0 - 320) / 32) in
  sp1 + 160 <= sp1 + 184 /\ sp1 + 200 <= sp1 + 206 /\ sp1 + 216 <= sp0 - 104 /\ sp0 - 352 < sp1 /\
  F + 512 <= sp1 /\ shadow_addr F + 64 <= sp1 /\
  (F + 512 <= shadow_addr F \/ shadow_addr F + 64 <= F).
Proof.
intros sp0 F H16 Hc H4 HF Happ sp1. subst sp1.
pose proof (Z.div_mod (sp0 - 320) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as M.
pose proof asan_consts as ((CVlo & CVhi) & _).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as F8.
pose proof (Z.div_le_upper_bound F 8 F ltac:(lia) ltac:(lia)) as F8u.
pose proof (Z.mul_div_le F 8 ltac:(lia)) as F8l.
unfold shadow_addr, SHADOW_OFF in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
destruct Happ as [Hlo | Hhi]; [left; lia | right; lia].
Qed.
End s.
