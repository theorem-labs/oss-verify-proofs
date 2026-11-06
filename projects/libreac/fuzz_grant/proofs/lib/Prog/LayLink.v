From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Image.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcPorts RcLay ctrl_lay_block_c
  GrantSweepModel RgLemmas RgNeeds_c.
Import ListNotations.
Open Scope Z_scope.

(* The headamp row of CTRL_FRAMES: kind 2 (template), template at 0x1055c, put offset 18, put length 3. *)
Lemma row_k : ly_k CTRL_ROW_BYTES = 2. Proof. vm_compute. reflexivity. Qed.
Lemma row_tm : ly_tm CTRL_ROW_BYTES = 0x1055c. Proof. vm_compute. reflexivity. Qed.
Lemma row_ao : ly_ao CTRL_ROW_BYTES = 18. Proof. vm_compute. reflexivity. Qed.
Lemma row_al : ly_al CTRL_ROW_BYTES = 3. Proof. vm_compute. reflexivity. Qed.

(* The 32 template bytes are read-only image bytes. *)
Lemma t32_ro : ro_bytes rsegs 0x1055c T32.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

(* A writable stack range and a read-only byte range never overlap. *)
Lemma stk_ro_dj : forall m lo hi A bs,
  stk rsegs m lo hi -> mem_inv rsegs m -> ro_bytes rsegs A bs -> (0 < length bs)%nat -> lo < hi ->
  ly_dj lo hi A (A + Z.of_nat (length bs)).
Proof.
  intros m lo hi A bs HS HM HR Hn Hlh. unfold ly_dj.
  destruct (Z_le_gt_dec hi A) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (A + Z.of_nat (length bs)) lo) as [H2|H2]; [right; exact H2|].
  exfalso. destruct HS as (Hlo & Hhi & HS).
  set (x := Z.max lo A).
  assert (Hx : lo <= x < hi) by (unfold x; lia).
  destruct (HS x Hx) as [Hw _].
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E.
  - pose proof (ro_bytes_nth rsegs bs A (Z.to_nat (x - A)) b HR E) as [_ Hro].
    replace (A + Z.of_nat (Z.to_nat (x - A))) with x in Hro by (unfold x; lia).
    destruct (m (wa x)) as [c|] eqn:Em.
    + rewrite (HM _ _ Em) in Hro. discriminate.
    + rewrite (wview_not_ro rsegs m (wa x) Hw Em) in Hro. discriminate.
  - apply nth_error_None in E. unfold x in E. lia.
Qed.

Lemma lay_eq : forall g zb ch p v, g <> 0 ->
  ly_lay 2 T32 zb g 18 3 (bl [ch; p; v]) = bl (lay_z ch p v).
Proof.
  intros g zb ch p v Hg. unfold ly_lay.
  replace (g =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hg).
  reflexivity.
Qed.

Theorem ctrl_lay_block_link : ctrl_lay_block_contract -> ctrl_lay_block_need.
Proof.
  intros LC. unfold ctrl_lay_block_contract, CTRL_LAY_BLOCK_K in LC.
  unfold ctrl_lay_block_need, CTRL_LAY_BLOCK_STACK, CTRL_ROW.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f lo ch p v blk -> -> -> Hf Hf50 Hg Hsp Hch Hp Hv HG HRW HMI HSTK Hlo HDb HDg HDgb HROW HDr HDrb.
  pose proof (bv_unsigned_in_range _ sp) as Rsp. pose proof (bv_unsigned_in_range _ a3) as Ra3.
  change (bv_modulus 64) with (2 ^ 64) in Rsp, Ra3.
  destruct (stk_split rsegs m lo (bv_unsigned sp - 240) (bv_unsigned sp) HSTK ltac:(lia)) as [HSlo Htop].
  assert (HBLK : stk rsegs m (f + 18) (f + 50)).
  { pose proof (stk_of_rw_cells rsegs m (f + 18) _ HRW) as H.
    assert (E : Z.of_nat (cells_size [CB 32 blk]) = 32) by reflexivity.
    rewrite E in H. replace (f + 18 + 32) with (f + 50) in H by lia. exact H. }
  assert (Htm_s : ly_dj (bv_unsigned sp - 240) (bv_unsigned sp) 0x1055c (0x1055c + 32)).
  { exact (stk_ro_dj m _ _ 0x1055c T32 Htop HMI t32_ro ltac:(cbn; lia) ltac:(lia)). }
  assert (Htm_b : ly_dj (f + 18) (f + 50) 0x1055c (0x1055c + 32)).
  { exact (stk_ro_dj m _ _ 0x1055c T32 HBLK HMI t32_ro ltac:(cbn; lia) ltac:(lia)). }
  eapply evt_mono.
  { apply (LC ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 0x1e2b0) (Z_to_bv 64 0) a3
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             f 0x1e2b0 0 (bv_unsigned a3) CTRL_ROW_BYTES blk T32 [] [] (bl [ch; p; v])).
    all: rewrite ?row_k, ?row_tm, ?row_ao, ?row_al.
    all: first
      [ reflexivity
      | exact Htop | exact HROW | exact HRW | exact HMI
      | (symmetry; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned)
      | (intros _; exact Htm_s) | (intros _; exact Htm_b)
      | (intros _; split; [lia | split; [reflexivity | exact t32_ro]])
      | (intros _ _; split; [reflexivity | split; [exact HG | unfold ly_dj; lia]])
      | (intros _ _; unfold ly_dj; lia)
      | (unfold ly_dj; lia)
      | (intros; exfalso; lia)
      | lia ]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              -> & MU & WM & MI & HS' & HB').
  rewrite row_k, row_ao, row_al, (lay_eq (bv_unsigned a3) _ ch p v Hg) in HB'.
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx |- *. tauto. }
  split; [exact WM|].
  split; [exact MI|].
  split.
  { apply (stk_merge rsegs m' lo (bv_unsigned sp - 240) (bv_unsigned sp)); [| exact HS' | lia].
    eapply stk_transport_disjoint; [exact HSlo | exact MU | exact WM |].
    cbn [disjoint_from]. repeat split; lia. }
  split.
  { eapply row_keep; [exact HROW | exact MU |]. unfold CTRL_ROW. cbn [disjoint_from]. repeat split; lia. }
  exact HB'.
Qed.
