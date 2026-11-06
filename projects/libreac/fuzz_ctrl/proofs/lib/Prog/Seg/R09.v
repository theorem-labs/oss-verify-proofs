(* Segment R09 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13398, 0x133c8], K13398 -> K133cc (b = 3, 4,
   reac_ctrl_identity_reply(Φ, n_b, sp+1824, sp+1688, sp+40)), K133d4 (b = 5, 6), K13428 (b <= 2);
   #7 not taken (RTM: k_b = 5 for b = 3, 4). libreac v1.9.0: round_trip addr / pl / pll sp+1720 / 1672 / 1776 ->
   sp+1824 / 1688 / 40 (table 7a), frame 1936. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcReply
  reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b2 Tac_b2m.
Import ListNotations.
Open Scope Z_scope.

(* b = 5, 6: blt 4 < b to 0x133d4. *)
Lemma r09_hi :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : Z),
    s1 = Z_to_bv 64 b -> b = 5 \/ b = 6 ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x133d4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13398) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b -> Hb.
  destruct Hb as [-> | ->]; step; step; if_true; apply evt_done; eexists; reflexivity.
Qed.

(* b = 0, 1, 2: bgeu b - 3 >=u 2 to 0x13428. *)
Lemma r09_lo :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : Z),
    s1 = Z_to_bv 64 b -> 0 <= b <= 2 ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13428) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13398) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b -> Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2) by lia.
  destruct E as [-> | [-> | ->]]; step; step; if_false; step; step; step; if_true;
    apply evt_done; do 2 eexists; reflexivity.
Qed.

(* b = 3, 4: k_b = 5, then the reply call. *)
Lemma r09_rep : reac_ctrl_identity_reply_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi n b k : Z) (g ja jp jn : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 b -> s4 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 n -> a0 = Z_to_bv 64 k ->
    k = 5 -> b = 3 \/ b = 4 ->
    65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 < phi -> phi + 50 <= spv - 160 -> 50 <= n < 2 ^ 64 ->
    stk rsegs m (spv - 160) spv -> mem_inv rsegs m -> length g = 50%nat -> bytes_at rsegs m phi g ->
    ir n g = true ->
    rw_cells rsegs m (spv + 1824) [Cells.CB 2 ja] -> rw_cells rsegs m (spv + 1688) [Cells.CB 8 jp] ->
    rw_cells rsegs m (spv + 40) [Cells.CB 8 jn] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x133cc) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x133cc) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1824, spv + 1824 + 2); (spv + 1688, spv + 1688 + 8); (spv + 40, spv + 40 + 8);
                (spv - 160, spv)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1824) (reply_addr g) /\
         bytes_at rsegs m' (spv + 1688) (le8 (Z_to_bv 64 (phi + 38))) /\
         bytes_at rsegs m' (spv + 40) (le8 (Z_to_bv 64 (r_pll g))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13398) fc None m (seg_rom rsegs)).
Proof.
  intros REPLY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi n b k g ja jp jn -> -> -> -> -> Hk Hb Hsp0 Hsp H16 Hph0 Hph Hn Hst MI Hlen HG Hir HA HPp HPn.
  subst k.
  destruct (b2_reply_ok phi n (spv + 1824) (spv + 1688) (spv + 40) g ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              Hir) as [OK RET].
  destruct Hb as [-> | ->].
  all: step; step; if_false; step; step; step; if_false; step; step; if_false.
  all: step; step; step; step; step; step.
  all: eapply evt_cut;
    [ eapply REPLY with (fr := phi) (len := n) (pa := spv + 1824) (pp := spv + 1688) (pn := spv + 40) (S := spv)
        (g := g) (ja := ja) (jp := jp) (jn := jn);
      unfold REAC_CTRL_IDENTITY_REPLY_K;
      first [ reflexivity | lia | exact Hst | exact MI | exact Hlen
            | intros _ _; split; [lia|]; split; [exact HG | left; lia]
            | intros _;
              split; [apply b2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
              split; [apply b2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
              split; [apply b2_mod; [exact H16 | lia | reflexivity | reflexivity]|];
              split; [exact HA|]; split; [exact HPp|]; split; [exact HPn|];
              repeat split; lia ]
    | ].
  all: intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                   E & MUc & WMc & _ & _ & HZ).
  all: subst ms'; rewrite RET.
  all: unfold reac_ctrl_identity_reply_fp, REAC_CTRL_IDENTITY_REPLY_K in MUc; rewrite OK in MUc;
    cbn [app] in MUc.
  all: destruct (HZ OK) as (HA' & HP' & HN').
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end.
  all: apply evt_done; do 15 eexists; split; [reflexivity|].
  all: split; [eapply munch_weaken; [|exact MUc]; intros x Hx; cbn [outside] in *; lia|]; split; [exact WMc|].
  all: split; [exact (sl_rw_bytes _ _ _ _ HA')|]; split; [exact (sl_rw_bytes _ _ _ _ HP')|].
  all: exact (sl_rw_bytes _ _ _ _ HN').
Qed.

Section R09.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis REPLY : reac_ctrl_identity_reply_contract.

Lemma seg_R09 : forall b, Hat B APIf ra (Inv_K133cc_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_K133d4_at B APIf ra empty) b -> Hat B APIf ra (Inv_K13428_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_K13398_at B APIf ra empty) b.
Proof.
  intros b H1 H2 H3 g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & H10 & HBp).
  pose proof HRF as ((HRB & Hnz & H20 & HF) & H22).
  pose proof HRB as (Hb6 & _ & _ & _ & H9 & _).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (b1_hb B APIf ra empty FF g phi (rnb g b) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
  destruct (b1_RS_len (g_in g) b) as (LI & LF).
  unfold rnb, rFb, rgb in *.
  destruct (b1_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HL).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hc : (b <= 2)%nat \/ (b = 3 \/ b = 4)%nat \/ (b = 5 \/ b = 6)%nat) by lia.
  destruct Hc as [Hlo | [Hmid | Hhi]].
  - (* b <= 2: K13428 *)
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of. apply r09_lo with (b := Z.of_nat b); [exact H9 | lia].
    + intros ms (a1' & a2' & ->). do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
      intros x _ O. exfalso. apply O. exact I.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (a1' & a2' & HE). injection HE; intros; subst.
      apply H3. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KR : b2_kr regs' regs).
      { unfold b2_kr, b1_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
      split; [exact (b2_RFx_keep g b _ _ phi regs regs' mem (normalize rsegs mem) m' [] HMI (munch_refl _ _) Hrel
                       LI LF I I KR HRF)|].
      split; [exact Hlo|]. unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). exact H10.
  - (* b = 3, 4: the reply, K133cc *)
    assert (Hbz : Z.of_nat b = 3 \/ Z.of_nat b = 4) by lia.
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1824) 2 ST ltac:(lia) ltac:(lia)) as (ja & HA).
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1688) 8 ST ltac:(lia) ltac:(lia)) as (jp & HPp).
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 40) 8 ST ltac:(lia) ltac:(lia)) as (jn & HPn).
    assert (ST160 : stk rsegs (normalize rsegs mem) (g_S g - 1936 - 160) (g_S g - 1936))
      by (apply (b2_stk_sub _ _ _ _ _ ST); lia).
    assert (HG : bytes_at rsegs (normalize rsegs mem) phi (rt_g (g_in g) (Z.of_nat b))).
    { apply b2_fr50_at; [exact (bytes_at_normalize rsegs mem phi _ HMI HF) | lia]. }
    pose proof (b2_rtm_ir (g_in g) (Z.of_nat b) Hbz) as Hir.
    pose proof (b2_rtm_k5 (g_in g) (Z.of_nat b) ltac:(lia)) as Hk.
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of.
      apply (r09_rep REPLY) with (spv := g_S g - 1936) (phi := phi) (n := rt_n (g_in g) (Z.of_nat b))
        (b := Z.of_nat b) (k := rt_k (g_in g) (Z.of_nat b)) (g := rt_g (g_in g) (Z.of_nat b))
        (ja := ja) (jp := jp) (jn := jn);
        [exact Hsp | exact H9 | exact H20 | exact H22 | exact H10 | exact Hk | exact Hbz | lia | lia | exact H16
        | lia | lia | lia | exact ST160 | exact (mem_inv_normalize rsegs mem) | apply fr50_length | exact HG
        | exact Hir | exact HA | exact HPp | exact HPn].
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      eexists. split; [exact MU|]. split; [exact WM|].
      intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HA' & HP' & HN').
      injection HE; intros; subst.
      apply H1. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KR : b2_kr regs' regs).
      { unfold b2_kr, b1_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
      split.
      { apply (b2_RFx_keep g b _ _ phi regs regs' mem m'' m' _ HMI MU Hrel LI LF); [| | exact KR | exact HRF];
          cbn [disjoint_from]; unfold spk, fsp, SLOT_FRAME, rnb; lia. }
      split; [exact Hmid|]. split; [exact Hk|]. split; [exact Hir|].
      unfold rg, q64 in *. rewrite (sl_getr_eqv _ _ _ Hx).
      split; [reflexivity|].
      split; [exact (b1_out _ _ _ _ Hrel HA')|]. split; [exact (b1_out _ _ _ _ Hrel HP')|].
      exact (b1_out _ _ _ _ Hrel HN').
  - (* b = 5, 6: K133d4 *)
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of. apply r09_hi with (b := Z.of_nat b); [exact H9 | lia].
    + intros ms (a1' & ->). do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
      intros x _ O. exfalso. apply O. exact I.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (a1' & HE). injection HE; intros; subst.
      apply H2. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KR : b2_kr regs' regs).
      { unfold b2_kr, b1_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
      split; [exact (b2_RFx_keep g b _ _ phi regs regs' mem (normalize rsegs mem) m' [] HMI (munch_refl _ _) Hrel
                       LI LF I I KR HRF)|].
      split; [exact Hhi|]. unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). exact H10.
Qed.

End R09.
