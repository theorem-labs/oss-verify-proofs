(* Segment R13 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13508, 0x13560], U13508 (b = 0, 1, 2) -> U135f8
   (b = 1, 2: `bnez s1`) or U13564 (b = 0: k_0 = 9 (#12 not taken), the room value of AF9, the 32-turn block sum loop
   (head 0x13534, counter a3 = 32 - i; T05 at 0x13538 not taken: Φ + 18 + i does not wrap, HBR), blocksum X(0) = 0
   (#13 not taken), reac_box_catalogue_match(Φ, n_0) = m by RTM). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u2 Tac_u2m.
Import ListNotations.
Open Scope Z_scope.

(* The loop at 0x13534, turn i (k = 32 - i turns left): a0 = Φ[18] + ... + Φ[17 + i], a1 = Φ + 18 + i,
   a2 = 2^64 - 18 - Φ, a3 = k, s8 = 32. *)
Lemma r13_loop : forall (bs : list byte) (phi : Z) (k i : nat)
  (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (1 <= k)%nat -> (i + k = 32)%nat -> 4096 <= phi -> phi + 50 < 2 ^ 63 ->
  (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  evt rsegs
    (fun ms' => exists a3' a4', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (RcModel.psum bs 32))
                   (Z_to_bv 64 (phi + 50)) (Z_to_bv 64 (18446744073709551598 - phi)) a3' a4' a5 a6 a7
                   s2 s3 s4 s5 s6 s7 (Z_to_bv 64 32) s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x13550) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (RcModel.psum bs i)) (Z_to_bv 64 (phi + 18 + Z.of_nat i))
             (Z_to_bv 64 (18446744073709551598 - phi)) (Z_to_bv 64 (Z.of_nat k)) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (Z_to_bv 64 32) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13534) fc None m (seg_rom rsegs)).
Proof.
  intros bs phi k. induction k as [|k IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m
      Hk Hik Hphi Hhi Hrd; [lia|].
  pose proof (Hrd i ltac:(lia)) as HR.
  pose proof (u2_psum_rng bs i) as Hps.
  step. step. u2_if_false. step. step. step. step. step.
  rewrite u2_zxb_u.
  destruct (Nat.eq_dec k 0) as [-> | Hk0].
  - assert (Ei : i = 31%nat) by lia. subst i.
    u2_if_false.
    replace (phi + 18 + Z.of_nat 31 + 1) with (phi + 50) by lia.
    rewrite <- (u2_psum_S bs 31).
    apply evt_done. do 2 eexists. reflexivity.
  - u2_if_true.
    replace (phi + 18 + Z.of_nat i + 1) with (phi + 18 + Z.of_nat (S i)) by lia.
    replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
    rewrite <- (u2_psum_S bs i).
    apply (IH (S i)); [lia | lia | lia | lia | exact Hrd].
Qed.

(* b = 1, 2: bnez b to 0x135f8. *)
Lemma r13_nz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : Z),
    s1 = Z_to_bv 64 b -> 0 < b <= 2 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                t3 t4 t5 t6)
                  F (Z_to_bv 64 0x135f8) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13508) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b -> Hb.
  assert (E : b = 1 \/ b = 2) by lia.
  destruct E as [-> | ->]; step; if_true; apply evt_done; reflexivity.
Qed.

(* b = 0: k_0 = 9, the block sum, the match call. *)
Lemma r13_zero : reac_box_catalogue_match_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi n k : Z) (bs fb : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 0 -> s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 n ->
    s8 = Z_to_bv 64 32 -> a0 = Z_to_bv 64 k ->
    k = 9 -> 65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    4096 <= phi -> phi + 50 <= spv - 240 -> phi + 50 < 2 ^ 63 -> 50 <= n < 2 ^ 64 ->
    (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
    RcModel.psum bs 32 mod 256 = 0 ->
    stk rsegs m (spv - 240) spv -> (forall a, spv - 240 <= a < spv -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat -> bytes_at rsegs m phi fb ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13564) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T n fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 (Z_to_bv 64 32) s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13564) fc None m' (seg_rom rsegs) /\
         munch [(spv - 240, spv)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13508) fc None m (seg_rom rsegs)).
Proof.
  intros MATCH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi n k bs fb -> -> -> -> -> -> Hk Hsp0 Hsp H16 Hph0 Hph Hhi Hn Hrd Hsum ST Hrom Lfb HF Hcat MI.
  subst k.
  step. if_false.
  step. step. if_false.
  step. step. step. step. step. step. step. step.
  rewrite u2_room by lia.
  eapply evt_cut.
  { replace (phi + 18) with (phi + 18 + Z.of_nat 0) by lia.
    apply (r13_loop bs phi 32 0); [lia | lia | lia | lia | exact Hrd]. }
  intros ms' (a3' & a4' & ->).
  pose proof (u2_psum_rng bs 32) as Hps.
  step. step.
  rewrite MState.unsigned_lit by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  replace (RcModel.psum bs 32 mod 2 ^ 8) with 0 by (rewrite <- Hsum; reflexivity).
  if_false.
  step. step. step.
  eapply evt_cut.
  { eapply MATCH with (f := phi) (len := n) (S := spv) (fb := fb); unfold CM_K;
      first [ reflexivity | lia | exact ST | exact Lfb | exact Hcat | exact MI | exact Hrom
            | intros _; split; [lia|]; split; [lia|]; split; [exact HF | left; lia] ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3'' & a4'' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & _ & _).
  subst ms'. unfold CM_K in MU.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in *; lia|]. exact WM.
Qed.

Section R13.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MATCH : reac_box_catalogue_match_contract.

Lemma seg_R13 : forall b : nat, (b = 0%nat -> Hcut B APIf ra (Inv_U13564 B APIf ra empty)) ->
  Hat B APIf ra (Inv_U135f8_at B APIf ra empty) b -> Hat B APIf ra (Inv_U13508_at B APIf ra empty) b.
Proof.
  intros b H0 He g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & Hb2 & H10).
  pose proof HRF as ((HRB & Hnz & H20 & HF) & H21).
  pose proof HRB as (Hb6 & _ & _ & (H8 & _ & _ & H24 & _) & _ & H9 & HID & HFG).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & HREL & _).
  destruct (u2_hb B APIf ra empty FF g phi (rnb g b) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
  destruct (u2_RS_len (g_in g) b) as (LI & LF).
  unfold rnb, rFb, rgb in *.
  destruct (u2_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HL).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (Nat.eq_dec b 0) as [Hb0 | Hb0].
  - (* b = 0: U13564 *)
    subst b. specialize (H0 eq_refl). change (Z.of_nat 0) with 0 in *.
    pose proof (u2_rtm_k0 (g_in g)) as Hk.
    pose proof (u2_rtm_sum (g_in g) 0 ltac:(lia)) as Hs.
    pose proof Hs as Hs'. rewrite <- u2_blocksum in Hs'.
    pose proof (u2_rtm_want (g_in g)) as Hw.
    pose proof (bytes_at_normalize rsegs mem phi _ HMI HF) as HFn.
    assert (HG : bytes_at rsegs (normalize rsegs mem) phi (rt_g (g_in g) 0)).
    { apply u2_fr50_at; [exact HFn | lia]. }
    assert (ST240 : stk rsegs (normalize rsegs mem) (g_S g - 1936 - 240) (g_S g - 1936))
      by (apply (u2_stk_sub _ _ _ _ _ ST); lia).
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of.
      apply (r13_zero MATCH) with (spv := g_S g - 1936) (phi := phi) (n := rt_n (g_in g) 0) (k := rt_k (g_in g) 0)
        (bs := skipn 18 (rt_g (g_in g) 0)) (fb := rt_g (g_in g) 0);
        [exact Hsp | exact H9 | exact H20 | exact H21 | exact H24 | exact H10 | exact Hk | lia | lia | exact H16
        | lia | lia | lia | lia | | exact Hs' | exact ST240 | | apply fr50_length | exact HG | |
        exact (mem_inv_normalize rsegs mem)].
      * intros j Hj. exact (u2_rd_blk _ phi (rt_F (g_in g) 0) j HFn ltac:(lia) Hj).
      * intros a Ha. apply u2_rom_none. unfold SL_TOP. lia.
      * intros a Ha. unfold CM_T in Ha. apply (u2_relro_mrd B APIf ra empty FF mem a HREL). lia.
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM).
      do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      eexists. split; [exact MU|]. split; [exact WM|].
      intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _).
      injection HE; intros; subst.
      apply H0. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KR : u2_ks regs' regs).
      { unfold u2_ks, u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; exact (eq_sym H24). }
      split.
      { apply (u2_RFx_keep g 0 _ _ phi regs regs' mem m'' m' _ HMI MU Hrel LI LF); [| | exact KR | exact HRF].
        - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
        - cbn [disjoint_from]. unfold rnb. change (Z.of_nat 0) with 0. lia. }
      split; [exact Hk|]. split; [unfold rgb; change (Z.of_nat 0) with 0; exact Hs|].
      unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). change CM_T with CAT. rewrite Hw. reflexivity.
  - (* b = 1, 2: U135f8 *)
    eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
    + rewrite sl_mkR_of. apply r13_nz with (b := Z.of_nat b); [exact H9 | lia].
    + intros ms ->. do 3 eexists. split; [reflexivity|].
      split; [|split; [reflexivity | split; reflexivity]].
      exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
      intros z _ O. exfalso. apply O. exact I.
    + intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
      injection HQ; intros; subst.
      apply He. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KR : u2_ks regs' regs).
      { unfold u2_ks, u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
      split; [exact (u2_RFx_keep g b _ _ phi regs regs' mem (normalize rsegs mem) m' [] HMI (munch_refl _ _) Hrel
                       LI LF I I KR HRF)|].
      split; [lia|]. unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). exact H10.
Qed.

End R13.
