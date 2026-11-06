From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem Cells Frame Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require PropExec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c GrantSlotPlan SlotImg SlotIntegration.
Import ListNotations.
Local Open Scope Z_scope.

Lemma row_rom : forall i, (i < 24)%nat ->
  seg_rom rsegs (wa (CTRL_HEADAMP_ROW + Z.of_nat i)) = nth_error CTRL_HEADAMP_BYTES i.
Proof.
  intros i Hi. do 24 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma row_in_relro : forall i, (i < 24)%nat -> in_globals frame_RELRO (CTRL_HEADAMP_ROW + Z.of_nat i).
Proof.
  intros i Hi. exists 0x1ed20, 424. split; [left; reflexivity|]. unfold CTRL_HEADAMP_ROW. lia.
Qed.

Lemma entry_present : forall m a, 0x51000 <= a < 2 ^ 64 -> wview rsegs m (wa a) <> None ->
  exists b, m (wa a) = Some b.
Proof.
  intros m a Ha H. destruct (m (wa a)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply H. unfold wview. rewrite E. rewrite wa_unsigned by lia. rewrite find_segment_rsegs_high by lia.
  reflexivity.
Qed.

Lemma entry_stk : forall mem' lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> find_segment rsegs a 1 = None /\ YO0d.present mem' a) ->
  stk rsegs (MemNorm.normalize rsegs mem') lo hi.
Proof.
  intros mem' lo hi Hlo Hhi H. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha.
  destruct (H a Ha) as [Hf [b Hb]].
  assert (Ero : ro_addr rsegs (wa a) = false) by (unfold ro_addr; rewrite wa_unsigned by lia; rewrite Hf; reflexivity).
  assert (En : MemNorm.normalize rsegs mem' (wa a) = Some b) by (unfold MemNorm.normalize; rewrite Ero; exact Hb).
  split; [unfold wview; rewrite En; discriminate | exists b; unfold mrd; rewrite En; reflexivity].
Qed.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HB : ms_segs B = rsegs.
Hypothesis FA : frame_allocator B API.

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (p n : Z).

Hypothesis HA0 : forall q k, In (q, k) (user_blocks A0) ->
  4096 <= ptr_addr L0 q /\ ptr_addr L0 q + k <= alloc_ceiling /\
  (forall i, 0 <= i < k -> ~ in_img B (ptr_addr L0 q + i)).

Theorem entry_holds : entry_ok B API L0 A0 regs0 mem0 md0 p n.
Proof.
  unfold entry_ok. intros ra empty pl b Hpre HG Hro Hemp.
  destruct Hpre as ((MR & WF & BD & INI & Hra & Hsp16 & Hspc & Hsp63 & Hwin & Htp & Herrw & Hp & Hn & Hpay & Hrod) &
                    Hnl & Hbd & Hres & Hroom & Hsink & Hfd & Hfs & Hsp47).
  pose proof alloc_ceiling_value as (Hceil & _).
  assert (Hro' : MemNorm.ro_agree rsegs mem0) by (rewrite <- HB; exact Hro).
  assert (HSL : LLVM_STACK = 8800) by reflexivity.
  assert (HSS : SLOT_STACK = 65536) by reflexivity.
  assert (Hpp : (n = 0 /\ p = 0x30150) \/ (0 < n /\ exists q, In (q, n) (user_blocks A0) /\ ptr_addr L0 q = p))
    by (subst empty; exact Hpay).
  assert (HPB : 0 < p /\ p + n <= alloc_ceiling /\
                (forall i, 0 <= i < n -> ~ in_img B (p + i)) /\
                (n = 0 -> in_img B p)).
  { destruct Hpp as [[-> ->] | (Hn0 & q & Hq & <-)].
    - split; [lia|]. split; [lia|]. split; [intros i Hi; lia|].
      intros _. apply (proj2 (in_img_rsegs B _ HB)). lia.
    - destruct (HA0 q n Hq) as (H1 & H2 & H3). split; [lia|]. split; [lia|]. split; [exact H3|]. lia. }
  destruct HPB as (Hp0 & Hpc & Himg & Hpimg).
  assert (Hnn : 0 <= n) by (rewrite Hnl; lia).
  assert (Hrowp : p + n <= CTRL_HEADAMP_ROW \/ CTRL_HEADAMP_ROW + 24 <= p).
  { destruct Hpp as [[-> ->] | (Hn0 & _)]; [unfold CTRL_HEADAMP_ROW; lia|].
    destruct (Z_le_gt_dec (p + n) CTRL_HEADAMP_ROW) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (CTRL_HEADAMP_ROW + 24) p) as [L2|L2]; [right; exact L2|].
    exfalso. apply (Himg (Z.max 0 (CTRL_HEADAMP_ROW - p))); [lia|].
    apply (proj2 (in_img_rsegs B _ HB)). unfold CTRL_HEADAMP_ROW in *. lia. }
  assert (HPC : rw_cells rsegs (MemNorm.normalize rsegs mem0) p [CB (length pl) pl]).
  { split; [split|].
    - cbn. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply MemNorm.bytes_at_normalize; [exact Hro'|].
      split; [lia|]. split; [lia|]. intros i Hi.
      pose proof (Hbd (Z.of_nat i) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb. rewrite HB in Hb. exact Hb.
    - cbn [cells_size csize]. rewrite Nat.add_0_r.
      destruct Hpp as [[En _] | (Hn0 & q & Hq & Hqp)].
      + assert (E0 : length pl = 0%nat) by lia. rewrite E0. split; [lia|]. split; [lia|]. intros i Hi. lia.
      + apply (MemNorm.wr_at_norm rsegs mem0 (MemNorm.normalize rsegs mem0) p _
                 (MemNorm.mem_rel_normalize rsegs mem0 Hro')).
        * split; [lia|]. split; [lia|]. intros i Hi.
          destruct FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BW & _).
          assert (Hin : In (p, n) (blocks L0 A0)).
          { unfold blocks. apply in_map_iff. exists (q, n). cbn [fst snd]. rewrite Hqp. split; [reflexivity | exact Hq]. }
          pose proof (BW L0 A0 mem0 md0 p n i MR Hin ltac:(lia)) as Hw.
          unfold YP09.writable_at in Hw. rewrite HB in Hw. exact Hw.
        * intros i Hi. unfold ro_addr. rewrite wa_unsigned by lia.
          rewrite (noimg_noseg B _ HB (Himg i ltac:(lia))). reflexivity. }
  assert (HSTK : stk rsegs (MemNorm.normalize rsegs mem0) (spZ regs0 - LLVM_STACK) (spZ regs0)).
  { apply entry_stk; [lia | lia |].
    intros a Ha.
    assert (Hfa : find_segment rsegs a 1 = None) by (apply find_segment_rsegs_high; lia).
    split; [exact Hfa|].
    pose proof (Hwin a ltac:(lia)) as Hw. unfold YP09.writable_at in Hw. rewrite HB in Hw.
    exact (entry_present mem0 a ltac:(lia) Hw). }
  assert (HROW : bytes_at rsegs (MemNorm.normalize rsegs mem0) CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES).
  { apply MemNorm.bytes_at_normalize; [exact Hro'|].
    split; [unfold CTRL_HEADAMP_ROW; lia|]. split; [cbn [length CTRL_HEADAMP_BYTES map]; unfold CTRL_HEADAMP_ROW; lia|].
    intros i Hi. change (length CTRL_HEADAMP_BYTES) with 24%nat in Hi.
    pose proof (HG (CTRL_HEADAMP_ROW + Z.of_nat i) (row_in_relro i Hi)) as Hg.
    rewrite HB in Hg. rewrite <- (row_rom i Hi). exact Hg. }
  split.
  - unfold St. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [exact Hro'|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold alloc_state. split; [exact MR|]. split; [exact WF|]. split; [exact BD|]. split; [exact INI|].
      exact Hres. }
    split; [exact Herrw|].
    split.
    { unfold payload_blk, x_n, xent. cbn [x_pl x_p].
      destruct Hpp as [[En Ep] | (Hn0 & q & Hq & Hqp)].
      - left. split; [lia|]. rewrite Ep. apply (proj2 (in_img_rsegs B _ HB)). lia.
      - right. split; [lia|]. exists q. rewrite <- Hnl. split; [exact Hq | exact Hqp]. }
    unfold Rel0. cbn [ms_mem YK11.mkst].
    split; [intros a _; split; [reflexivity | tauto]|].
    split; [intros q k Hq; exists q; split; [exact Hq | reflexivity]|].
    split; [intros a Ha; pose proof (Hwin a ltac:(unfold S0 in Ha; lia)) as Hw; unfold YP09.writable_at in *;
            rewrite HB in Hw; exact Hw|].
    exists (m_vmmaps md0). apply with_vmmaps_self.
  - exists (YK11.mkst regs0 (Z_to_bv 64 ENTRY) (MemNorm.normalize rsegs mem0) (seg_rom rsegs)).
    split.
    + unfold At_entry, common, x_n, xent, S0.
      cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst
           x_S x_ra x_gp x_tp x_sv x_p x_pl x_F x_fc].
      repeat match goal with |- _ /\ _ => split end.
      all: try reflexivity.
      all: try (rewrite <- Hnl; first [exact HPC | lia]).
      all: try exact HPC.
      all: try exact HSTK.
      all: try exact HROW.
      all: try apply MemNorm.mem_inv_normalize.
      all: try exact Hsp16.
      all: try exact Hsp63.
      all: try (rewrite <- Hnl; rewrite HSL; lia).
      all: try (rewrite HSL; unfold CTRL_HEADAMP_ROW; lia).
      all: try lia.
      all: try (unfold rg, w64, spZ; cbn [ms_regs YK11.mkst]; symmetry; apply Z_to_bv_bv_unsigned).
      all: try (unfold rg; cbn [ms_regs YK11.mkst]; exact Hp).
      all: try (unfold rg, w64; cbn [ms_regs YK11.mkst]; rewrite <- Hnl; exact Hn).
    + unfold MemNorm.ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
      repeat match goal with |- _ /\ _ => split end; try reflexivity.
      apply MemNorm.mem_rel_normalize. exact Hro'.
Qed.

End E.
