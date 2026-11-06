(* Segment R05 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x133e8, 0x13408], U133e8 -> U1340c
   (turn b) (n_b = reac_ctrl_build_as(out = sp+192, m, b, our = sp+114, round_trip.box, 0x1234, 0, 0); ba_tbl at
   0x209c8 and the row m from frame_RELRO; window 320). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcEmit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcBox RcLay RcPorts RcEmitLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u1.
Import ListNotations.
Open Scope Z_scope.

(* build_as' width n and frame length (n_b when md = m, mb = its row). *)
Definition r05_n (md : Z) (mb : list byte) : Z := RcPorts.bm_uw md (firstn 8 (skipn 16 mb)).
Definition r05_N (md : Z) (mb : list byte) (b : Z) : Z :=
  if ba_E (r05_n md mb) mb b then 52 + 36 * r05_n md mb else 0.

Lemma r05_evt : reac_ctrl_build_as_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv md b : Z) (mb nb db junk : list byte),
    sp = Z_to_bv 64 spv -> s0 = Z_to_bv 64 md -> s1 = Z_to_bv 64 b -> s2 = Z_to_bv 64 0x105c9 ->
    s3 = Z_to_bv 64 0x1234 ->
    0x100000 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 -> 0 <= b <= 6 ->
    0 < md -> md + 296 <= 0x53000 -> md mod 8 = 0 ->
    stk rsegs m (spv - 320) spv ->
    bytes_at rsegs m (BA_FR + 72) ba_tbl ->
    length db = 6%nat -> bytes_at rsegs m (spv + 114) db ->
    bytes_at rsegs m 0x105c9 box6 ->
    length mb = 296%nat -> bytes_at rsegs m md mb ->
    ((b = 5 \/ b = 6) /\ RcSynth.has mb <> 0 /\ RcSynth.rname mb <> 0 ->
       RcBox.name_ok nb /\ bytes_at rsegs m (RcSynth.rname mb) nb /\ 0 <= RcSynth.rname mb /\
       RcSynth.rname mb + 17 <= 0x53000) ->
    (ba_E (r05_n md mb) mb b = true ->
       rw_cells rsegs m (spv + 192) [Cells.CB (Z.to_nat (52 + 36 * r05_n md mb)) junk] /\
       52 + 36 * r05_n md mb <= 1492) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x1340c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (r05_N md mb b))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x1340c) fc None m' (seg_rom rsegs) /\
         munch [(spv - 320, spv); (spv + 192, spv + 192 + r05_N md mb b)] m m' /\ wmono rsegs m m' /\
         (ba_E (r05_n md mb) mb b = true ->
            bytes_at rsegs m' (spv + 192)
              (em_fr db box6 (bv_unsigned (Z_to_bv 64 0x1234) mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234)
                 (ba_X md mb nb b) (52 + 36 * r05_n md mb))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x133e8) fc None m (seg_rom rsegs)).
Proof.
  intros BUILD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv md b mb nb db junk -> -> -> -> -> Hsp0 Hsp H16 Hb Hmd0 Hmd Hmd8 ST HBA Hdb HD HS Hmb HM HNM HO MI.
  unfold r05_N, r05_n in *.
  assert (Hgo : ba_go (spv + 192) md b = true).
  { unfold ba_go. rewrite (proj2 (Z.eqb_neq (spv + 192) 0) ltac:(lia)), (proj2 (Z.eqb_neq md 0) ltac:(lia)),
      (proj2 (Z.leb_le b 6) ltac:(lia)). reflexivity. }
  step. step. step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply BUILD with (o := spv + 192) (md := md) (b := b) (d := spv + 114) (s := 0x105c9) (ns := 0)
      (mb := mb) (nb := nb) (db := db) (sb := box6) (junk := junk).
    all: unfold REAC_CTRL_BUILD_AS_K, BA_FR, RcLay.ly_dj in *.
    all: rewrite ?MState.unsigned_lit by lia.
    all: first
      [ reflexivity | exact ST | exact HBA | exact Hdb | exact HD | exact HS | exact MI
      | lia
      | (intros _; split; [exact Hmd8|]; split; [lia|]; split; [exact Hmb|]; split; [exact HM | lia])
      | (intros _ Hnm; destruct (HNM Hnm) as (N1 & N2 & N3 & N4); split; [exact N1|]; split; [exact N2|];
         destruct N1 as (L1 & _); lia)
      | (intros _; lia)
      | (intros HgE; rewrite Hgo in HgE; cbn [andb] in HgE; destruct (HO HgE) as (RW & Hlen);
         split; [exact RW|]; split; [lia|]; split; [lia|]; split; [lia|];
         split; [intros Hnm; destruct (HNM Hnm) as ((L1 & _) & _ & N3 & N4); lia|]; split; lia) ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & _ & _ & Hfr).
  subst ms'. rewrite Hgo in *. cbn [andb] in *.
  rewrite ?MState.unsigned_lit in MUc by lia. unfold REAC_CTRL_BUILD_AS_K in MUc.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MUc|]. split; [exact WMc|].
  intros HE. exact (proj1 (Hfr HE)).
Qed.

Section R05.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BUILD : reac_ctrl_build_as_contract.

Lemma seg_R05 : forall b, Hat B APIf ra (Inv_U1340c_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_U133e8_at B APIf ra empty) b.
Proof.
  intros b H g c (L & A & regs & mem & md & -> & HFR & HP & HRS).
  pose proof HRS as (Hb6 & (Hc7 & Hcp & Hcn) & HOUR & (H8 & H18 & H19 & H24 & H25 & H26 & H27) & HM8 & H9 & HID & HFG).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & HREL & _).
  destruct (u1_RS_len (g_in g) b) as (LI & LF).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  pose proof (u1_istar_rng (g_in g)) as Hi.
  pose proof (u1_mrow (g_in g)) as (Hmr & Hm32 & Hm8).
  assert (HN : 0 <= rt_n (g_in g) (Z.of_nat b) <= 1492).
  { destruct (Z.eq_dec (rt_n (g_in g) (Z.of_nat b)) 0) as [E0|E0]; [lia|].
    destruct (u1_rtn _ _ E0) as (_ & R & _). lia. }
  pose proof (bytes_at_normalize rsegs mem _ _ HMI (u1_ba_bytes B APIf ra empty FF mem HREL)) as HBA.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI (u1_row_bytes B APIf ra empty FF mem _ HREL Hi)) as HM.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HOUR) as HD.
  assert (HS : bytes_at rsegs (normalize rsegs mem) 0x105c9 box6).
  { apply (ro_bytes_at rsegs); [apply mem_inv_normalize | lia | cbn; lia |].
    exact (Image.ro_bytes_b_sound rsegs _ _ u1_box_ro). }
  assert (HNM : (Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ RcSynth.has (rt_mb (g_in g)) <> 0 /\
                RcSynth.rname (rt_mb (g_in g)) <> 0 ->
     RcBox.name_ok (rt_nb (g_in g)) /\ bytes_at rsegs (normalize rsegs mem) (RcSynth.rname (rt_mb (g_in g)))
       (rt_nb (g_in g)) /\ 0 <= RcSynth.rname (rt_mb (g_in g)) /\ RcSynth.rname (rt_mb (g_in g)) + 17 <= 0x53000).
  { intros (_ & Hh & Hn). unfold rt_nb, rt_mb in *.
    destruct (u1_names (istar (g_in g)) Hi Hh Hn) as (N1 & N2 & N3 & N4).
    split; [exact N1|]. split; [|lia].
    destruct N1 as (L1 & _).
    apply (ro_bytes_at rsegs); [apply mem_inv_normalize | lia | lia |].
    exact (Image.ro_bytes_b_sound rsegs _ _ N2). }
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (HOb : exists junk, ba_E (rt_uw (g_in g)) (rt_mb (g_in g)) (Z.of_nat b) = true ->
     rw_cells rsegs (normalize rsegs mem) (g_S g - 1936 + 192) [Cells.CB (Z.to_nat (52 + 36 * rt_uw (g_in g))) junk] /\
     52 + 36 * rt_uw (g_in g) <= 1492).
  { destruct (ba_E (rt_uw (g_in g)) (rt_mb (g_in g)) (Z.of_nat b)) eqn:HE.
    - pose proof HE as HE'. unfold ba_E in HE'. apply andb_true_iff in HE' as [Ew _].
      destruct (RcEmitLib.em_wok_range _ Ew) as [R _].
      destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 192) (Z.to_nat (52 + 36 * rt_uw (g_in g))) ST
                  ltac:(lia) ltac:(lia)) as (junk & HC).
      exists junk. intros _. split; [exact HC | lia].
    - exists []. intros Hf. discriminate. }
  destruct HOb as (junk & HOb).
  assert (ST320 : stk rsegs (normalize rsegs mem) (g_S g - 1936 - 320) (g_S g - 1936)).
  { destruct ST as (S1 & S2 & S3). split; [lia|]. split; [lia|]. intros a Ha. apply S3. lia. }
  eapply (sl_mid B APIf ra empty FF g [] L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (r05_evt BUILD) with (spv := g_S g - 1936) (md := mrow (g_in g)) (b := Z.of_nat b)
      (mb := rt_mb (g_in g)) (nb := rt_nb (g_in g)) (db := OUR (g_in g)) (junk := junk);
      [exact Hsp | exact H8 | exact H9 | exact H18 | exact H19 | lia | lia | lia | lia
      | lia | unfold CAT, CAT_ROW in Hmr; lia | exact Hm8
      | exact ST320 | exact HBA | apply OUR_length | exact HD | exact HS | apply u1_row_len | exact HM
      | exact HNM | exact HOb | apply mem_inv_normalize].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists [(g_S g - 1936 - 320, g_S g - 1936);
            (g_S g - 1936 + 192, g_S g - 1936 + 192 + rt_n (g_in g) (Z.of_nat b))].
    split; [exact MU|]. split; [exact WM|].
    intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HZ).
    injection HE; intros; subst.
    apply H. exists L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split.
    { apply (u1_RB_keep g b _ _ regs regs' mem m'' m' _ HMI MU Hrel LI LF); [| |exact HRS].
      - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
      - unfold u1_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
    unfold rg, rnb, rFb. rewrite (sl_getr_eqv _ _ _ Hx).
    split; [reflexivity|].
    intros Hnz. destruct (u1_rtn _ _ Hnz) as (HEb & _ & _).
    unfold rt_F. replace (rt_n (g_in g) (Z.of_nat b)) with (52 + 36 * rt_uw (g_in g))
      by (unfold rt_n; rewrite HEb; reflexivity).
    exact (u1_out _ _ _ _ Hrel (HZ HEb)).
Qed.

End R05.
