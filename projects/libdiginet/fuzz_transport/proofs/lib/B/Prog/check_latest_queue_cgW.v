(* check_latest_queue_cgW: Theorem transport_check_latest_queue_cg_holds, the statement
   transport_check_latest_queue_cg_holds_stmt of lib/B/Prog/check_latest_queue_cg.v, the machine walk of
   check_latest_queue on fuzz_transport.asan-ubsan at 0x86104 (436 bytes). Image B's twin of
   lib/A/Prog/check_latest_queue_cgW.v: the same walk at image B's code, world table and kit.

   The walk is the caller-journal form:
   - an INNER journal is started at the entry state (lib/Reusable/YCbq.v ajournal_sub_init; stack window
     [spZ regs - CLQ_STK, spZ regs), no footprint, no frame of its own);
   - the function's own code runs as the four footprint runs of lib/B/Prog/check_latest_queue_seg_runs.v, carried
     into SRr by lib/B/Prog/DgnTransportBCgRun.v decode_run; the inner journal is re-established after the thirteen
     saves by YCbq.v ajournal_exec (the written bytes lie in the journal's own stack window) and after each run
     that writes nothing;
   - the bcmp wrapper is cut by YCbq.v aj_bcmp_at at the statement's abcmp_realizes premise; its result is 0
     because the two byte ranges agree, which is what the model's queue_loop says of the turn;
   - the loop is an induction on queue_loop's fuel: one turn is clq_run_body, the bcmp call and clq_run_ret, and
     the exit (i = g_nq, where the model's loop stops and the counter s4 is 0) is clq_run_exit;
   - the inner journal composes with the caller's by YCbq.v ajournal_sub, the kept bytes come from YCbq.v
     acall_kept_of_journal with an EMPTY written range (the function stores only into its own frame), and the
     meter is not charged.

   The world premise tw_at is read through aview; every footprint run reads raw memory, so clq_tw_raw turns the
   one into the other at each payload byte (a byte aview answers for is not hidden). The shadow bytes of the
   payloads of g_s, g_q and g_cmd are 0 at every state of the journal (trans_clq_cells through
   DgnTransportBCg.v decode_zshadow_rd), which is what makes the three instrumented checks fall through. The ubsan
   build's three checks fall through by the model's bounds (clq_step: i < 512, Q_at Bw i < 1024). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
PropExec MState Mem Cells Step Frame Regs6ss ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBAddr DgnTransportBCg DgnTransportBCgRun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
check_latest_queue_cg check_latest_queue_seg_facts check_latest_queue_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require KindB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.

(* A register of a state a run reached, read off the run's register map. *)
Ltac clq_reg EQV := etransitivity; [apply (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV); reflexivity | reflexivity].

Section clqw. Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* ------------------------------------------------------------------ *)
(* the world and the shadow, between aview and the machine's raw view  *)
(* ------------------------------------------------------------------ *)

(* Every payload byte of TMAP_B is a byte aview answers for, so it is not hidden and the machine's raw view
   reads the same byte. *)
Lemma clq_tw_raw : forall (W : world segs) (m : word -> option byte) (Bw : list byte),
  tw_at TMAP_B (aview segs (w_H W) m) Bw -> tw_at TMAP_B (csw_view m) Bw.
Proof.
  intros W m Bw [HL HR]. split; [exact HL|].
  intros o b n i Hin Hi. pose proof (HR o b n i Hin Hi) as H.
  unfold csw_view. rewrite <- (decode_aview_mrd W m (b + i)); [exact H|].
  exact (decode_aview_vis W m (b + i) _ H).
Qed.

(* The shadow bytes of a payload, at the aview of an AR state. *)
Definition clq_av_zsh (W : world segs) (m : word -> option byte) (lo n : Z) : Prop :=
  forall a, lo <= a < lo + n -> aview segs (w_H W) m (shadow_addr a) = Some 0.

Lemma clq_av_zsh_of : forall ly S (W : world segs) m md lo n,
  @AR rc segs B ly S W m md -> decode_zshadow_at B lo (lo + n) ->
  lo mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> clq_av_zsh W m lo n.
Proof.
  intros ly S W m md lo n HAR HZ Hlo Hn Hn0 a Ha.
  assert (E8 : 8 * (a / 8) = a - a mod 8) by (Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MB.
  pose proof (decode_zshadow_rd B ly S W m md lo (lo + n) (8 * (a / 8)) HAR
                ltac:(rewrite Z.mul_comm; apply Z_mod_mult)
                ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) HZ) as Hz.
  replace (shadow_addr a) with (shadow_addr (8 * (a / 8))); [exact Hz|].
  unfold shadow_addr, ASAN_K. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Lemma clq_zsh_of_av : forall (W : world segs) m lo n, clq_av_zsh W m lo n -> clq_zsh m lo n.
Proof.
  intros W m lo n H a Ha. pose proof (H a Ha) as Hz.
  pose proof (decode_aview_vis W m _ _ Hz) as Hv.
  rewrite (decode_aview_mrd W m (shadow_addr a) Hv) in Hz.
  destruct (mrd rsegs m (wa (shadow_addr a))) as [b0|] eqn:E; [|discriminate Hz].
  cbn [option_map] in Hz. injection Hz as Hz. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite Hz. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* the footprint                                                       *)
(* ------------------------------------------------------------------ *)

Lemma clq_rng_payload : forall (W : world segs) m (Bw : list byte) o b n lo len,
  tw_at TMAP_B (aview segs (w_H W) m) Bw -> In (o, b, n) TMAP_B ->
  b <= lo -> lo + len <= b + n -> 0 <= len ->
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros W m Bw o b n lo len HW Hin H1 H2 H3.
  pose proof (tw_row TMAP_B o b n TMAP_B_ok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  apply (decode_rng W); [lia | lia |].
  intros x Hx. destruct HW as [_ HR].
  pose proof (HR o b n (x - b) Hin ltac:(lia)) as Hv.
  replace (b + (x - b)) with x in Hv by lia.
  exact (decode_aview_vis W m x _ Hv).
Qed.

Lemma clq_rng_shadow : forall (W : world segs) m lo n,
  clq_av_zsh W m lo n -> 0 <= lo -> lo mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> lo + n <= 2 ^ 47 ->
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (shadow_addr lo) (n / 8).
Proof.
  intros W m lo n HZ Hlo0 Hlo Hn Hn0 Htop.
  unfold shadow_addr, ASAN_K.
  apply (decode_rng W); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |].
  intros x Hx.
  assert (Ha : lo <= 8 * (x - 0x7fff8000) < lo + n) by (Z.div_mod_to_equations; lia).
  pose proof (HZ _ Ha) as Hv.
  replace (shadow_addr (8 * (x - 0x7fff8000))) with x in Hv;
    [exact (decode_aview_vis W m x _ Hv)|].
  unfold shadow_addr, ASAN_K. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma clq_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [Hh [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

Lemma clq_av_zsh_mono : forall (W : world segs) m lo n n',
  clq_av_zsh W m lo n -> n' <= n -> clq_av_zsh W m lo n'.
Proof. intros W m lo n n' H Hn a Ha. apply H. lia. Qed.

(* A range inside a payload whose shadow is 0 is addressable. *)
Lemma clq_ra_of_av : forall (W : world segs) m lo n x len,
  clq_av_zsh W m lo n -> lo <= x -> x + len <= lo + n ->
  range_addressable (aview segs (w_H W) m) SHADOW_OFF x len.
Proof.
  intros W m lo n x len HZ H1 H2 a Ha.
  exists 0. split; [|left; reflexivity].
  replace (shadow_of_addr SHADOW_OFF a) with (shadow_addr a); [apply HZ; lia|].
  unfold shadow_of_addr, shadow_addr, ASAN_K, SHADOW_OFF. lia.
Qed.

(* ... and the aligned group of 8 shadow bytes around it is visible, when the payload starts and ends on a
   64-byte boundary (the hull of a range inside it is a range of its own shadow). *)
Lemma clq_hull_of_av : forall (W : world segs) m lo n x len,
  clq_av_zsh W m lo n -> 0 <= lo -> lo mod 64 = 0 -> n mod 64 = 0 ->
  lo <= x -> x + len <= lo + n -> 0 < len ->
  shadow_hull_vis (aview segs (w_H W) m) x len.
Proof.
  intros W m lo n x len HZ Hlo0 H64 Hn64 H1 H2 H3 s Hs.
  unfold YG0f.shadow_addr, SHADOW_OFF in Hs.
  assert (Ha : lo <= 8 * (s - 2147450880) < lo + n) by (Z.div_mod_to_equations; lia).
  pose proof (HZ _ Ha) as Hv.
  replace (shadow_addr (8 * (s - 2147450880))) with s in Hv.
  - rewrite Hv. discriminate.
  - unfold shadow_addr, ASAN_K. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the inner post of the walk                                          *)
(* ------------------------------------------------------------------ *)

Definition clq_ret_post (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
    (mdc : Model) (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (@YKK.mkst fx regs2 (ret_pc (YKK.getr regs (Z_to_bv 5 1))) mem2 (YKK.seg_rom segs)) md2 /\
    ajournal CLQ_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 /\
    aregs_preserved regs regs2.

(* ------------------------------------------------------------------ *)
(* what a state of the walk gives the bcmp wrapper                     *)
(* ------------------------------------------------------------------ *)

(* A range inside one payload is readable by a callee, and lies below the stack. *)
Lemma clq_src_ok : forall (W : world segs) m (Bw : list byte) o b n (regsT : bvmap 5 word) x len,
  tw_at TMAP_B (aview segs (w_H W) m) Bw -> In (o, b, n) TMAP_B ->
  b <= x -> x + len <= b + n -> x + len <= 2 ^ 32 -> 2 ^ 33 <= spZ regsT ->
  src_ok segs W regsT m x len.
Proof.
  intros W m Bw o b n regsT x len HTW Hin H1 H2 H3 H4 a Ha.
  pose proof (tw_row TMAP_B o b n TMAP_B_ok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  split.
  - destruct HTW as [_ HR]. replace a with (b + (a - b)) by lia.
    rewrite (HR o b n (a - b) Hin ltac:(lia)). discriminate.
  - unfold ESTACK. lia.
Qed.

(* The two byte ranges the bcmp wrapper compares agree, because the model says their world bytes do. *)
Lemma clq_bytes_eq : forall (W : world segs) m (Bw : list byte) o1 b1 n1 o2 b2 n2 k1 k2 (len : Z),
  tw_at TMAP_B (aview segs (w_H W) m) Bw -> In (o1, b1, n1) TMAP_B -> In (o2, b2, n2) TMAP_B ->
  0 <= k1 -> k1 + len <= n1 -> 0 <= k2 -> k2 + len <= n2 -> 0 <= len ->
  TW.zs (TW.sub Bw (o1 + k1) (Z.to_nat len)) = TW.zs (TW.sub Bw (o2 + k2) (Z.to_nat len)) ->
  forall j, 0 <= j < len ->
    aview segs (w_H W) m (b1 + k1 + j) = aview segs (w_H W) m (b2 + k2 + j).
Proof.
  intros W m Bw o1 b1 n1 o2 b2 n2 k1 k2 len HTW Hin1 Hin2 Hk1 Hk1n Hk2 Hk2n Hlen HZ j Hj.
  pose proof (tw_row TMAP_B o1 b1 n1 TMAP_B_ok Hin1) as (Ho1 & Hn1 & HoW1 & Hb1 & Hb164).
  pose proof (tw_row TMAP_B o2 b2 n2 TMAP_B_ok Hin2) as (Ho2 & Hn2 & HoW2 & Hb2 & Hb264).
  destruct HTW as [HL HR].
  assert (HLZ : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
  replace (b1 + k1 + j) with (b1 + (k1 + j)) by lia.
  replace (b2 + k2 + j) with (b2 + (k2 + j)) by lia.
  rewrite (HR o1 b1 n1 (k1 + j) Hin1 ltac:(lia)), (HR o2 b2 n2 (k2 + j) Hin2 ltac:(lia)).
  f_equal.
  pose proof (f_equal (fun l => nth (Z.to_nat j) l 0) HZ) as HN. cbv beta in HN.
  unfold TW.zs in HN.
  rewrite (nth_indep (map bv_unsigned (TW.sub Bw (o1 + k1) (Z.to_nat len))) 0
             (bv_unsigned (Z_to_bv 8 0))) in HN
    by (rewrite length_map, TWorldLemmas.length_sub by lia; lia).
  rewrite (nth_indep (map bv_unsigned (TW.sub Bw (o2 + k2) (Z.to_nat len))) 0
             (bv_unsigned (Z_to_bv 8 0))) in HN
    by (rewrite length_map, TWorldLemmas.length_sub by lia; lia).
  rewrite !map_nth in HN.
  rewrite (tw_nth_sub Bw (o1 + k1) (Z.to_nat len) (Z.to_nat j) (Z_to_bv 8 0) ltac:(lia) ltac:(lia)
             ltac:(lia)) in HN.
  rewrite (tw_nth_sub Bw (o2 + k2) (Z.to_nat len) (Z.to_nat j) (Z_to_bv 8 0) ltac:(lia) ltac:(lia)
             ltac:(lia)) in HN.
  replace (Z.to_nat (o1 + (k1 + j))) with (Z.to_nat (o1 + k1) + Z.to_nat j)%nat by lia.
  replace (Z.to_nat (o2 + (k2 + j))) with (Z.to_nat (o2 + k2) + Z.to_nat j)%nat by lia.
  exact HN.
Qed.


(* ------------------------------------------------------------------ *)
(* the loop                                                            *)
(* ------------------------------------------------------------------ *)

(* From the head of turn i, with the model's queue_loop still answering Some true, the function returns and the
   inner journal reaches the return state. The induction is on queue_loop's fuel: the exit (i = g_nq) is
   clq_run_exit, a turn is clq_run_body, the bcmp wrapper and clq_run_ret. *)
Lemma clq_loop :
  transport_cells B -> trans_clq_cells B -> AR_laws segs B ->
  (forall fx' : YKK.FPState,
     @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  forall (fuel : nat) (lyc : alayout) (Sc : astate) (W : world segs)
         (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word)
         (Bw : list byte) (i : Z) (m : word -> option byte) (md : Model) (junk : list byte)
         (regsH : bvmap 5 word),
    ajournal CLQ_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W m md 0 ->
    tw_at TMAP_B (aview segs (w_H W) m) Bw ->
    rw_cells rsegs m (spZ regs + -112)
      (clq_frame_cells junk (YKK.getr regs (Z_to_bv 5 1)) (YKK.getr regs (Z_to_bv 5 8))
         (YKK.getr regs (Z_to_bv 5 9)) (YKK.getr regs (Z_to_bv 5 18)) (YKK.getr regs (Z_to_bv 5 19))
         (YKK.getr regs (Z_to_bv 5 20)) (YKK.getr regs (Z_to_bv 5 21)) (YKK.getr regs (Z_to_bv 5 22))
         (YKK.getr regs (Z_to_bv 5 23)) (YKK.getr regs (Z_to_bv 5 24)) (YKK.getr regs (Z_to_bv 5 25))
         (YKK.getr regs (Z_to_bv 5 26)) (YKK.getr regs (Z_to_bv 5 27))) ->
    2 ^ 46 <= spZ regs <= 2 ^ 47 ->
    YKK.getr regs (Z_to_bv 5 3) = w64 (as_gp B) ->
    YKK.getr regs (Z_to_bv 5 4) = w64 (as_tp B) ->
    YKK.getr regsH (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -112) ->
    YKK.getr regsH (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3) ->
    YKK.getr regsH (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4) ->
    YKK.getr regsH (Z_to_bv 5 8) = Z_to_bv 64 (6159672 + 32 * i) ->
    YKK.getr regsH (Z_to_bv 5 9) = Z_to_bv 64 (6232192 + 4 * i) ->
    YKK.getr regsH (Z_to_bv 5 10) = Z_to_bv 64 (6159648 + 32 * i) ->
    YKK.getr regsH (Z_to_bv 5 18) = Z_to_bv 64 1024 ->
    YKK.getr regsH (Z_to_bv 5 19) = Z_to_bv 64 40 ->
    YKK.getr regsH (Z_to_bv 5 20) = Z_to_bv 64 (TW.g_nq Bw - i) ->
    YKK.getr regsH (Z_to_bv 5 21) = Z_to_bv 64 2147450880 ->
    YKK.getr regsH (Z_to_bv 5 22) = Z_to_bv 64 (6232192 + 4 * i) ->
    YKK.getr regsH (Z_to_bv 5 23) = Z_to_bv 64 (2052 - 4 * i) ->
    YKK.getr regsH (Z_to_bv 5 24) = Z_to_bv 64 6180992 ->
    YKK.getr regsH (Z_to_bv 5 25) = Z_to_bv 64 (2148220839 + 4 * i) ->
    YKK.getr regsH (Z_to_bv 5 26) = Z_to_bv 64 18446744073703370623 ->
    (forall j, 0 <= j < TW.g_nq Bw -> TW.S_queue_len Bw j <= 24) ->
    TC.queue_loop fuel Bw i true = Some true ->
    0 <= i <= TW.g_nq Bw ->
    SRr segs W (@cfg_at fx segs CLQ_HEAD regsH m md) (clq_ret_post lyc Sc W memc mdc regs).
Proof.
intros HCELLS HZC LAWS BCMP fuel.
assert (HSTKv : CLQ_STK = 8304) by reflexivity.
induction fuel as [|fuel IH]; intros lyc Sc W memc mdc regs Bw i m md junk regsH
  HJ HTW HFR HSP HGPB HTPB E2 E3 E4 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25 E26 HLEN24 HQL Hi;
  [discriminate HQL|].
pose proof HJ as (HARm & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres
  & Hstatic & F5 & HQT).
pose proof HZC as (ZSs & ZQs & ZCs).
pose proof (clq_av_zsh_of lyc Sc W m md TB_g_s TW.SZ_g_s HARm ZSs eq_refl eq_refl
  ltac:(unfold TW.SZ_g_s; lia)) as AVS.
pose proof (clq_av_zsh_of lyc Sc W m md TB_g_q TW.SZ_g_q HARm ZQs eq_refl eq_refl
  ltac:(unfold TW.SZ_g_q; lia)) as AVQ.
pose proof (clq_av_zsh_of lyc Sc W m md TB_g_cmd TW.SZ_g_cmd HARm ZCs eq_refl eq_refl
  ltac:(unfold TW.SZ_g_cmd; lia)) as AVC.
unfold TB_g_s, TB_g_q, TB_g_cmd, TW.SZ_g_s, TW.SZ_g_q, TW.SZ_g_cmd in AVS, AVQ, AVC.
pose proof (clq_zsh_of_av W m 6157888 18264 AVS) as ZS.
pose proof (clq_zsh_of_av W m 6232192 4096 AVQ) as ZQ.
pose proof (clq_zsh_of_av W m 6180992 40960 AVC) as ZC.
pose proof (clq_tw_raw W m Bw HTW) as HTWr.
pose proof (TWorldLemmas.u_at_range Bw TW.OFF_g_nq 4) as Rnq.
change (TW.u_at Bw TW.OFF_g_nq 4) with (TW.g_nq Bw) in Rnq.
change (8 * Z.of_nat 4) with 32 in Rnq.
assert (RFR : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (spZ regs + -112) 112).
{ apply (decode_rng W); [lia | lia |].
  intros b Hb. destruct (Hpres b ltac:(lia)) as [Hh _]. exact Hh. }
assert (RQ : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) 6232192 4096)
  by (apply (clq_rng_payload W m Bw TW.OFF_g_q TB_g_q TW.SZ_g_q);
      [exact HTW | exact TMAP_B_g_q | unfold TB_g_q; lia | unfold TB_g_q, TW.SZ_g_q; lia | lia]).
assert (RS : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) 6157888 18264)
  by (apply (clq_rng_payload W m Bw TW.OFF_g_s TB_g_s TW.SZ_g_s);
      [exact HTW | exact TMAP_B_g_s | unfold TB_g_s; lia | unfold TB_g_s, TW.SZ_g_s; lia | lia]).
assert (RC : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) 6180992 40960)
  by (apply (clq_rng_payload W m Bw TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd);
      [exact HTW | exact TMAP_B_g_cmd | unfold TB_g_cmd; lia | unfold TB_g_cmd, TW.SZ_g_cmd; lia | lia]).
assert (RSQ : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) 2148229904 512)
  by exact (clq_rng_shadow W m 6232192 4096 AVQ ltac:(lia) eq_refl eq_refl ltac:(lia) ltac:(lia)).
assert (RSS : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) 2148220616 2283)
  by exact (clq_rng_shadow W m 6157888 18264 AVS ltac:(lia) eq_refl eq_refl ltac:(lia) ltac:(lia)).
assert (RSC : ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) 2148223504 5120)
  by exact (clq_rng_shadow W m 6180992 40960 AVC ltac:(lia) eq_refl eq_refl ltac:(lia) ltac:(lia)).
destruct (Z_le_gt_dec (TW.g_nq Bw) i) as [Hge|Hlt].
- (* the counter is 0: the epilogue and the return *)
  assert (Hie : i = TW.g_nq Bw) by lia.
  eapply (@decode_run fx W regsH m md CLQ_HEAD).
  { unfold LCK.ms_of_regs.
    eapply (clq_run_exit _ (spZ regs)); [lia | exact E2 | | exact HFR | exact RFR].
    rewrite E20. f_equal. lia. }
  intros ms' md' (ms0 & HP & EQV) SBM.
  unfold clq_post_exit in HP.
  destruct HP as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31
                  & Hms0).
  subst ms0.
  rewrite (decode_ms_shape _ _ _ _ EQV).
  apply SRr_ret. unfold clq_ret_post.
  split; [reflexivity|].
  exists (ms_regs ms'), m, md'.
  split; [reflexivity|].
  split.
  { apply (@ajournal_exec rc tfib_sink_head segs B LAWS decode_segs_low CLQ_STK (spZ regs) []
             lyc Sc W memc mdc [] lyc Sc W m md 0 m md' (fun _ => False) HJ);
      [ intros x _; reflexivity | apply YK1b.mem_grows_refl | intros x _; reflexivity | exact SBM
      | intros a Ha; destruct Ha ]. }
  intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + transitivity (Z_to_bv 64 (spZ regs)); [clq_reg EQV|]. unfold spZ. apply Z_to_bv_bv_unsigned.
  + transitivity (YKK.getr regsH (Z_to_bv 5 3)); [clq_reg EQV | exact E3].
  + transitivity (YKK.getr regsH (Z_to_bv 5 4)); [clq_reg EQV | exact E4].
  + clq_reg EQV. (* s0 .. s11 and the return address are the frame's, which the epilogue reloads *)
  + clq_reg EQV.
  + clq_reg EQV.
  + clq_reg EQV.
  + clq_reg EQV.
  + clq_reg EQV.
  + clq_reg EQV.
  + clq_reg EQV.
  + clq_reg EQV.
  + clq_reg EQV.
  + clq_reg EQV.
  + clq_reg EQV.
- (* one turn of the loop *)
  destruct (clq_step fuel Bw i HQL ltac:(lia)) as (HiC & HqC & HiQ & HLN & HBY & HQL1).
  unfold TC.CMDS_MAX, TC.QUEUE_MAX in HiC, HqC, HiQ.
  assert (Hqz : 0 <= TW.Q_at Bw i) by (unfold TW.Q_at; apply TWorldLemmas.u_at_range).
  assert (HL24 : TW.S_queue_len Bw i <= 24) by (apply HLEN24; lia).
  assert (HL0 : 0 <= TW.S_queue_len Bw i)
    by (unfold TW.S_queue_len; apply TWorldLemmas.u_at_range).
  eapply (@decode_run fx W regsH m md CLQ_HEAD).
  { unfold LCK.ms_of_regs.
    eapply (clq_run_body _ (spZ regs) (TW.g_nq Bw - i) i Bw);
      [ exact E2 | exact E8 | exact E9 | exact E10 | exact E18 | exact E19 | exact E20 | exact E21
      | exact E22 | exact E23 | exact E24 | exact E25 | exact E26 | exact HTWr | exact ZQ | exact ZS
      | exact ZC | lia | lia | lia | lia | lia | exact HLN | exact RQ | exact RSQ | exact RS | exact RSS
      | exact RC | exact RSC ]. }
  intros msA mdA (ms0 & HP & EQVA) SBMA.
  unfold clq_post_body in HP.
  destruct HP as (y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & Hms0).
  subst ms0.
  rewrite (decode_ms_shape _ _ _ _ EQVA).
  assert (JA : ajournal CLQ_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W m mdA 0).
  { apply (@ajournal_exec rc tfib_sink_head segs B LAWS decode_segs_low CLQ_STK (spZ regs) []
             lyc Sc W memc mdc [] lyc Sc W m md 0 m mdA (fun _ => False) HJ);
      [ intros x _; reflexivity | apply YK1b.mem_grows_refl | intros x _; reflexivity | exact SBMA
      | intros a Ha; destruct Ha ]. }
  assert (G1 : YKK.getr (ms_regs msA) (Z_to_bv 5 1) = Z_to_bv 64 CLQ_BCMP_RET) by clq_reg EQVA.
  assert (G2 : YKK.getr (ms_regs msA) (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -112)) by clq_reg EQVA.
  assert (G3 : YKK.getr (ms_regs msA) (Z_to_bv 5 3) = YKK.getr regsH (Z_to_bv 5 3)) by clq_reg EQVA.
  assert (G4 : YKK.getr (ms_regs msA) (Z_to_bv 5 4) = YKK.getr regsH (Z_to_bv 5 4)) by clq_reg EQVA.
  assert (G10 : YKK.getr (ms_regs msA) (Z_to_bv 5 10) = Z_to_bv 64 (6159648 + 32 * i)) by clq_reg EQVA.
  assert (G11 : YKK.getr (ms_regs msA) (Z_to_bv 5 11)
                = Z_to_bv 64 (6180992 + TW.Q_at Bw i * 40 + 12)) by clq_reg EQVA.
  assert (G12 : YKK.getr (ms_regs msA) (Z_to_bv 5 12)
                = Z_to_bv 64 (TW.S_queue_len Bw i)) by clq_reg EQVA.
  assert (GSP : spZ (ms_regs msA) = spZ regs + -112).
  { change (spZ (ms_regs msA)) with (bv_unsigned (YKK.getr (ms_regs msA) (Z_to_bv 5 2))).
    rewrite G2, unsigned_lit by lia. reflexivity. }
  eapply SRr_bind.
  { eapply (aj_bcmp_at segs B LAWS decode_segs_low _ (BCMP fx) W (ms_regs msA) m
              CLQ_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc mdA 0
              (6159648 + 32 * i) (6180992 + TW.Q_at Bw i * 40 + 12) (TW.S_queue_len Bw i) (-112)
              (Z_to_bv 64 CLQ_BCMP_RET) JA).
    - exact G10.
    - exact G11.
    - exact G12.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact GSP.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - etransitivity; [exact G3 | rewrite E3; exact HGPB].
    - etransitivity; [exact G4 | rewrite E4; exact HTPB].
    - exact G1.
    - apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - apply (clq_src_ok W m Bw TW.OFF_g_s TB_g_s TW.SZ_g_s);
        [exact HTW | exact TMAP_B_g_s | unfold TB_g_s; lia | unfold TB_g_s, TW.SZ_g_s; lia | lia | lia].
    - apply (clq_src_ok W m Bw TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd);
        [exact HTW | exact TMAP_B_g_cmd | unfold TB_g_cmd; lia | unfold TB_g_cmd, TW.SZ_g_cmd; lia
        | lia | lia].
    - intros a Ha. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - left. unfold kLowMemEnd. lia.
    - left. unfold kLowMemEnd. lia.
    - apply (clq_ra_of_av W m 6157888 18264 _ _ AVS); lia.
    - intros Hn0. apply (clq_hull_of_av W m 6157888 18240 _ _
        (clq_av_zsh_mono W m 6157888 18264 18240 AVS ltac:(lia))); try lia; reflexivity.
    - apply (clq_ra_of_av W m 6180992 40960 _ _ AVC); lia.
    - intros Hn0. apply (clq_hull_of_av W m 6180992 40960 _ _ AVC); try lia; reflexivity. }
  cbv beta. intros W' c2 _ (-> & regs2 & mem2 & md2 & v & Hc2 & JB & HPRESb & HRESb & HIFF & HKEEP & HPRb).
  assert (HV0 : v = w64 0).
  { apply HIFF. intros j Hj.
    replace (6159648 + 32 * i + j) with (TB_g_s + (1760 + 32 * i) + j) by (unfold TB_g_s; lia).
    replace (6180992 + TW.Q_at Bw i * 40 + 12 + j) with (TB_g_cmd + (40 * TW.Q_at Bw i + 12) + j)
      by (unfold TB_g_cmd; lia).
    apply (clq_bytes_eq W m Bw TW.OFF_g_s TB_g_s TW.SZ_g_s TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd
             (1760 + 32 * i) (40 * TW.Q_at Bw i + 12) (TW.S_queue_len Bw i) HTW TMAP_B_g_s
             TMAP_B_g_cmd ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(lia)
             ltac:(unfold TW.SZ_g_cmd; lia) ltac:(lia)); [|lia].
    rewrite HLN.
    replace (TW.OFF_g_s + (1760 + 32 * i)) with (TW.A_S_queue_bytes i)
      by (unfold TW.A_S_queue_bytes; lia).
    replace (TW.OFF_g_cmd + (40 * TW.Q_at Bw i + 12)) with (TW.A_Cmd_bytes (TW.Q_at Bw i))
      by (unfold TW.A_Cmd_bytes; lia).
    exact HBY. }
  subst c2.
  change (SRr segs W (@cfg_at fx segs CLQ_BCMP_RET regs2 mem2 md2)
            (clq_ret_post lyc Sc W memc mdc regs)).
  (* the world and the frame survive the call: both lie outside its stack window *)
  assert (HTW2 : tw_at TMAP_B (aview segs (w_H W) mem2) Bw).
  { destruct HTW as [HL HR]. split; [exact HL|]. intros o b n j Hin Hj.
    pose proof (tw_row TMAP_B o b n TMAP_B_ok Hin) as (Ho & Hn & HoW & Hb & Hb64).
    pose proof (TMAP_B_hull (b + j) ltac:(exists o, b, n; split; [exact Hin | lia])) as Hhull.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hhull.
    rewrite (HKEEP (b + j) ltac:(lia) ltac:(unfold ESTACK; lia)). exact (HR o b n j Hin Hj). }
  assert (HFR2 : rw_cells rsegs mem2 (spZ regs + -112)
    (clq_frame_cells junk (YKK.getr regs (Z_to_bv 5 1)) (YKK.getr regs (Z_to_bv 5 8))
       (YKK.getr regs (Z_to_bv 5 9)) (YKK.getr regs (Z_to_bv 5 18)) (YKK.getr regs (Z_to_bv 5 19))
       (YKK.getr regs (Z_to_bv 5 20)) (YKK.getr regs (Z_to_bv 5 21)) (YKK.getr regs (Z_to_bv 5 22))
       (YKK.getr regs (Z_to_bv 5 23)) (YKK.getr regs (Z_to_bv 5 24)) (YKK.getr regs (Z_to_bv 5 25))
       (YKK.getr regs (Z_to_bv 5 26)) (YKK.getr regs (Z_to_bv 5 27)))).
  { eapply (decode_frame_ext (spZ regs + -112) 112 _ m mem2);
      [ unfold clq_frame_cells; cbn [cells_size csize Nat.add]; lia | | exact HFR ].
    intros j Hj. unfold wa.
    apply (decode_present_eq W m mem2 (spZ regs + -112 + j));
      [ apply (Hpres (spZ regs + -112 + j)); lia
      | apply HPRb; apply (Hpres (spZ regs + -112 + j)); lia
      | apply HKEEP; [lia | unfold ESTACK; lia] ]. }
  (* the return of the wrapper: back to the head at i + 1 *)
  eapply (@decode_run fx W regs2 mem2 md2 CLQ_BCMP_RET).
  { unfold LCK.ms_of_regs.
    eapply (clq_run_ret _ (spZ regs) (TW.g_nq Bw - i) i).
    - rewrite (HPRESb 2 ltac:(unfold acallee_saved; lia)). exact G2.
    - transitivity v; [exact HRESb | exact HV0].
    - rewrite (HPRESb 8 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 9 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 18 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 19 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 20 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 21 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 22 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 23 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 24 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 25 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 26 ltac:(unfold acallee_saved; lia)). clq_reg EQVA.
    - rewrite (HPRESb 27 ltac:(unfold acallee_saved; lia)). clq_reg EQVA. }
  intros msB mdB (ms1 & HPB & EQVB) SBMB.
  destruct HPB as (b1' & Hms1). subst ms1.
  rewrite (decode_ms_shape _ _ _ _ EQVB).
  assert (JC : ajournal CLQ_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 mdB 0).
  { apply (@ajournal_exec rc tfib_sink_head segs B LAWS decode_segs_low CLQ_STK (spZ regs) []
             lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 mem2 mdB (fun _ => False) JB);
      [ intros x _; reflexivity | apply YK1b.mem_grows_refl | intros x _; reflexivity | exact SBMB
      | intros a Ha; destruct Ha ]. }
  (* the registers 3 and 4 are the entry's across msA, regs2 *)
  assert (Hc3 : YKK.getr regs2 (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3)).
  { transitivity (YKK.getr (ms_regs msA) (Z_to_bv 5 3));
      [apply (HPRESb 3); unfold acallee_saved; lia|].
    transitivity (YKK.getr regsH (Z_to_bv 5 3)); [clq_reg EQVA | exact E3]. }
  assert (Hc4 : YKK.getr regs2 (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4)).
  { transitivity (YKK.getr (ms_regs msA) (Z_to_bv 5 4));
      [apply (HPRESb 4); unfold acallee_saved; lia|].
    transitivity (YKK.getr regsH (Z_to_bv 5 4)); [clq_reg EQVA | exact E4]. }
  apply (IH lyc Sc W memc mdc regs Bw (i + 1) mem2 mdB junk (ms_regs msB) JC HTW2 HFR2 HSP HGPB HTPB).
  + clq_reg EQVB.
  + transitivity (YKK.getr regs2 (Z_to_bv 5 3)); [clq_reg EQVB | exact Hc3].
  + transitivity (YKK.getr regs2 (Z_to_bv 5 4)); [clq_reg EQVB | exact Hc4].
  + clq_reg EQVB. (* s0, s1, a0, s2, s3 *)
  + clq_reg EQVB.
  + clq_reg EQVB.
  + clq_reg EQVB.
  + clq_reg EQVB.
  + transitivity (Z_to_bv 64 (TW.g_nq Bw - i + -1)); [clq_reg EQVB | f_equal; lia].
  + clq_reg EQVB. (* s5 .. s10 *)
  + clq_reg EQVB.
  + clq_reg EQVB.
  + clq_reg EQVB.
  + clq_reg EQVB.
  + clq_reg EQVB.
  + exact HLEN24.
  + exact HQL1.
  + lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the statement of lib/B/Prog/check_latest_queue_cg.v                 *)
(* ------------------------------------------------------------------ *)

Lemma clq_holds : @transport_check_latest_queue_cg_holds_stmt fx rc B MT.
Proof.
  unfold transport_check_latest_queue_cg_holds_stmt.
  intros HCELLS HZC LAWS MTL BCMP.
  unfold transport_check_latest_queue_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw'
    HJ Hra Hra4 Hgp Htp Hsp16 Hlo Hhi HTW Hm HLEN24 Hev.
  assert (HSTKv : CLQ_STK = 8304) by reflexivity.
  assert (HFRv : CLQ_FR = 112) by reflexivity.
  (* the model *)
  destruct (clq_model Bw Bw' Hm) as (HBB & HSQ & HQL).
  (* the caller journal's facts *)
  pose proof HJ as (HARc & Hlyc & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone
    & Hpresc & Hstaticc & F5 & HQT).
  pose proof Hstaticc as (H16 & HSTK0c & Hceilc & Hsloc & Hshic & H47c & Hbot & Htop2 & Htop).
  (* the inner journal at the entry *)
  assert (JI0 : ajournal CLQ_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0).
  { apply (@ajournal_sub_init rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             CLQ_STK (spZ regs) [] (spZ regs - sp0) HJ ltac:(lia)
             ltac:(rewrite Zminus_mod, Hsp16, H16; reflexivity) ltac:(lia)
             ltac:(lia) ltac:(lia)). }
  pose proof JI0 as (HARi & Hlyi & Hsecsi & Hwlei & Hioi & Hfrsi & Hnevi & Hki & G1 & G2 & G3 & G4 & Hgonei
    & Hpres0 & Hstatic0 & G5 & HQTi).
  pose proof Hstatic0 as (H16i & HSTK0i & Hceil & Hsloi & Hshii & H47 & Hboti & Htop2i & Htopi).
  pose proof (@ASAN_CEIL_range rc) as HAC. unfold ASAN_CEIL in HAC.
  assert (HESTK : ESTACK = 4096) by reflexivity.
  assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  assert (ESP : bv_unsigned (YKK.getr regs (Z_to_bv 5 2)) = spZ regs) by reflexivity.
  (* the queue-length bound in g_nq form *)
  assert (HLENq : forall j, 0 <= j < TW.g_nq Bw -> TW.S_queue_len Bw j <= 24).
  { intros j Hj. apply HLEN24. rewrite HSQ. exact Hj. }
  assert (Hnq0 : 0 <= TW.g_nq Bw)
    by (change (TW.g_nq Bw) with (TW.u_at Bw TW.OFF_g_nq 4); apply TWorldLemmas.u_at_range).
  (* the entry run, to the loop head at i = 0 *)
  assert (HENT : transportb_sigma TB_check_latest_queue = CLQ_ENTRY) by (vm_compute; reflexivity).
  rewrite HENT.
  eapply (@decode_run fx W regs memc mdc CLQ_ENTRY).
  { unfold LCK.ms_of_regs. eapply clq_run_entry.
    - exact (clq_tw_raw W memc Bw HTW).
    - exact HSQ.
    - apply (clq_stk_present (w_H W) memc (spZ regs - 112) (spZ regs)); [lia | lia |].
      intros a Ha. apply Hpres0. lia.
    - lia.
    - exact HSP.
    - exact (decode_cells_asan B HCELLS lyc Sc W memc mdc (w_Hoff W) HARc).
    - apply (decode_rng W); [lia | lia |].
      intros b Hb. destruct (Hpres0 b ltac:(lia)) as [Hh _]. exact Hh.
    - apply (decode_rng W); [lia | lia |].
      intros b Hb. apply (decode_vis_seg W). apply (decode_covers_img 670960 8 b ltac:(decode_seg) ltac:(lia)).
    - apply (decode_rng W); [lia | lia |].
      intros b Hb. apply (decode_vis_seg W). apply (decode_covers_img 706168 8 b ltac:(decode_seg) ltac:(lia)).
    - apply (clq_rng_payload W memc Bw TW.OFF_g_s TB_g_s TW.SZ_g_s);
        [exact HTW | exact TMAP_B_g_s | unfold TB_g_s; lia | unfold TB_g_s, TW.SZ_g_s; lia | lia].
    - apply (clq_rng_payload W memc Bw TW.OFF_g_nq TB_g_nq TW.SZ_g_nq);
        [exact HTW | exact TMAP_B_g_nq | unfold TB_g_nq; lia | unfold TB_g_nq, TW.SZ_g_nq; lia | lia]. }
  intros ms' md' (ms0 & HP & EQV) SBM.
  unfold clq_post_entry in HP.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                  & junk & m' & Hms0 & MUe & WMe & FRe).
  subst ms0.
  rewrite ESP in MUe, FRe.
  rewrite (decode_ms_shape _ _ _ _ EQV).
  change (SRr segs W (@cfg_at fx segs CLQ_HEAD (ms_regs ms') m' md')
            (transport_clq_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw')).
  (* re-establish the inner journal after the thirteen saves *)
  assert (MUw : forall x : word, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) ->
            mrestrict (w_H W) m' x = mrestrict (w_H W) memc x).
  { intros x Hx. unfold mrestrict. rewrite (MUe x); [reflexivity|]. cbn [outside].
    split; [unfold spZ in *; lia | exact I]. }
  assert (MGw : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) m')).
  { intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 112)) as [Hl|Hl];
      [rewrite (MUe x); [exact Hx | cbn [outside]; split; [unfold spZ in *; lia | exact I]]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|rewrite (MUe x); [exact Hx | cbn [outside]; split; [unfold spZ in *; lia | exact I]]].
    assert (Hw : wview rsegs m' x <> None).
    { refine (WMe x _). unfold wview. destruct (memc x) as [b|] eqn:Em;
        [discriminate | exfalso; first [exact (Hx Em) | exact (Hx eq_refl)]]. }
    unfold wview in Hw. destruct (m' x) as [b|] eqn:Em1; [discriminate|]. exfalso.
    rewrite (find_segment_none rsegs (bv_unsigned x)) in Hw; [exact (Hw eq_refl)|].
    intros Him. pose proof (decode_segs_low _ Him) as Hlow. unfold kLowMemEnd in Hlow. lia. }
  assert (MHw : forall x : word, w_H W x = true -> m' x = memc x).
  { intros x Hx.
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 112)) as [Hl|Hl];
      [apply (MUe x); cbn [outside]; split; [unfold spZ in *; lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|apply (MUe x); cbn [outside]; split; [unfold spZ in *; lia | exact I]].
    exfalso. pose proof (proj1 (Hpres0 (bv_unsigned x) ltac:(lia))) as Hhx.
    rewrite Z_to_bv_bv_unsigned in Hhx. congruence. }
  assert (JH : ajournal CLQ_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W m' md' 0).
  { apply (@ajournal_exec rc tfib_sink_head segs B LAWS decode_segs_low CLQ_STK (spZ regs) []
             lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m' md' (fun a => spZ regs - 112 <= a < spZ regs)
             JI0 MUw MGw MHw SBM).
    intros a Ha. left. lia. }
  (* the frame cells at m', in the form clq_loop takes (registers read off the entry map) *)
  assert (FRh : rw_cells rsegs m' (spZ regs + -112)
    (clq_frame_cells junk (YKK.getr regs (Z_to_bv 5 1)) (YKK.getr regs (Z_to_bv 5 8))
       (YKK.getr regs (Z_to_bv 5 9)) (YKK.getr regs (Z_to_bv 5 18)) (YKK.getr regs (Z_to_bv 5 19))
       (YKK.getr regs (Z_to_bv 5 20)) (YKK.getr regs (Z_to_bv 5 21)) (YKK.getr regs (Z_to_bv 5 22))
       (YKK.getr regs (Z_to_bv 5 23)) (YKK.getr regs (Z_to_bv 5 24)) (YKK.getr regs (Z_to_bv 5 25))
       (YKK.getr regs (Z_to_bv 5 26)) (YKK.getr regs (Z_to_bv 5 27)))).
  { exact FRe. }
  (* the world at m': the prologue wrote only the frame, outside the payload hull *)
  assert (HTWm : tw_at TMAP_B (aview segs (w_H W) m') Bw).
  { destruct HTW as [HL HR]. split; [exact HL|]. intros o b n j Hin Hj.
    pose proof (tw_row TMAP_B o b n TMAP_B_ok Hin) as (Ho & Hn & HoW & Hb & Hb64).
    pose proof (TMAP_B_hull (b + j) ltac:(exists o, b, n; split; [exact Hin | lia])) as Hhull.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hhull.
    transitivity (aview segs (w_H W) memc (b + j)); [|exact (HR o b n j Hin Hj)].
    unfold aview, YP09.mbyte, mrestrict.
    rewrite (MUe (Z_to_bv 64 (b + j))); [reflexivity|].
    cbn [outside]. rewrite (unsigned_lit (b + j)) by lia.
    split; [unfold spZ in *; lia | exact I]. }
  (* the loop, then the post *)
  eapply SRr_mono.
  { apply (clq_loop HCELLS HZC LAWS BCMP (Datatypes.S (Z.to_nat TC.QUEUE_MAX))
             lyc Sc W memc mdc regs Bw 0 m' md' junk (ms_regs ms') JH HTWm FRh HSP Hgp Htp).
    - clq_reg EQV. (* sp, gp, tp, s0, s1, a0, s2, s3 *)
    - clq_reg EQV.
    - clq_reg EQV.
    - clq_reg EQV.
    - clq_reg EQV.
    - clq_reg EQV.
    - clq_reg EQV.
    - clq_reg EQV.
    - transitivity (Z_to_bv 64 (TW.g_nq Bw)); [clq_reg EQV | f_equal; lia].
    - clq_reg EQV. (* s5 .. s10 *)
    - clq_reg EQV.
    - clq_reg EQV.
    - clq_reg EQV.
    - clq_reg EQV.
    - clq_reg EQV.
    - exact HLENq.
    - exact HQL.
    - lia. }
  (* clq_ret_post -> transport_clq_post *)
  intros W2 c2 Hle (-> & regs2 & mem2 & md2 & Hc2 & JF & HPRES).
  unfold transport_clq_post, decode_cg_post.
  pose proof (KindB.ret_pc_of_ok (YKK.getr regs (Z_to_bv 5 1)) Hra) as ERA.
  exists lyc, Sc, regs2, mem2, md2, 0.
  split. { rewrite Hc2, ERA. reflexivity. }
  split; [unfold CLQ_EV; lia|].
  split.
  { replace (k + 0) with (k + (0 + 0)) by lia. change own with ([] ++ own).
    apply (ajournal_sub segs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             CLQ_STK (spZ regs) [] [] lyc Sc W mem2 md2 (0 + 0) HJ JF ltac:(lia) ltac:(lia)).
    intros a (r & Hr & _). destruct Hr. }
  split; [exact HPRES|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B decode_segs_low CLQ_STK (spZ regs) [] [] lyc Sc W memc mdc
             lyc Sc W mem2 md2 0 (fun _ => False) JF HARc).
    - intros a (r & Hr & _). destruct Hr.
    - intros b m i Hb _ _. exact Hb.
    - exact sink_closed_nil. }
  split; [exact (mo_le_refl MT MTL Sc) | exact HBB].
Qed.

End clqw.

Theorem transport_check_latest_queue_cg_holds :
  forall fx rc B MT, @transport_check_latest_queue_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@clq_holds fx rc B MT). Qed.

Print Assumptions transport_check_latest_queue_cg_holds.
