From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import LLVMFuzzerTestOneInput_top LLVMFuzzerTestOneInput_cfb read_name_ccf.
Import ListNotations.
Open Scope Z_scope.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MEMCPY : memcpy_contract.

Lemma top_payload_rng_cf : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
  llvm_ctx_cf B API stk empty L0 A0 regs0 mem0 md0 ra p n b -> 0 < n -> 4096 <= p /\ p + n <= YM05.alloc_ceiling.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b
    ((SEGS & _) & _ & _ & (HM0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _) & _) Hn.
  destruct Hpl as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 q n 0 HM0 Hq ltac:(lia)) as (_ & H1 & H2 & _).
  rewrite Hqp in H1, H2. lia.
Qed.

Theorem llvm_top_holds_cf : llvm_top_ok_cf B API.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b i k c HC HJ.
  pose proof HC as (BI & Hk & _ & Hpre & _).
  destruct BI as (SEGS & _ & _ & HGG & _ & AX).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & Hceil & H63 & _).
  destruct HJ as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & j0 & j1 & j2 &
    -> & Hfrm & Hbase & H10 & H18 & HS & Hi & Hinn & Hpip & Hipn & Hr & Hinv & Hfab & Halloc & Hk1).
  pose proof Halloc as (FR & Hmine & Hres).
  pose proof Hbase as (E2 & E3 & E4 & E8 & E22 & E23 & E24 & E25 & E26 & E27).
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR) as [Hh Hl].
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro).
  destruct (llvm_payload_read_cf B API stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md ip HC FR ltac:(lia))
    as [vb HR].
  destruct (top_payload_rng_cf stk empty L0 A0 regs0 mem0 md0 ra p n b HC ltac:(lia)) as [Hp1 Hp2].
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  unfold LLVM_K, LLVM_FRAME in Hk.
  destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + 287) HM Hmine ltac:(lia)) as (_ & _ & Hr1 & _).
  assert (HBr : bytes_at rsegs mem r bs) by exact (top_rw_bytes mem r 288 bs Hr).
  assert (HL : length bs = 288%nat) by (destruct Hinv as ((HL & _) & _); exact HL).
  assert (HSn : rw_cells rsegs (normalize rsegs mem) (spZ regs0 - 464)
    (CB 8 j0 :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 fab) :: CB 320 j1 :: C8 (Z_to_bv 64 ip) :: CB 8 j2 ::
     llvm_saved_cells regs0)).
  { apply (lf_rw_cells_norm B); [ exact SEGS | exact Hro | | exact HS ].
    intros x Hx Himg. pose proof (lf_in_img_top B _ SEGS Himg). lia. }
  unfold llvm_saved_cells in HSn.
  rewrite SEGS.
  eapply ((llvm_run_norm_cf B ltac:(segs_tac)) fx' regs (Z_to_bv 64 LLVM_TOP) mem md); [ exact Hh | exact Hl | exact Hro | | | ].
  - unfold Regs6ss.mkR_of, LLVM_TOP.
    eapply (llvm_top_evt MEMCPY) with (spv := spZ regs0 - 464) (r := r) (ip := ip) (inn := inn) (i := i)
      (fab := fab) (lo := spZ regs0 - stk) (hi := spZ regs0) (j0 := j0) (j1 := j1) (j2 := j2) (bs := bs) (vb := vb).
    + exact E2.
    + exact E8.
    + exact H18.
    + exact H10.
    + exact E22.
    + exact HSn.
    + exact (bytes_at_normalize rsegs mem r bs Hro HBr).
    + exact HL.
    + rewrite <- (ov_read_rel rsegs mem (normalize rsegs mem) _ _ (mem_rel_normalize rsegs mem Hro)). exact HR.
    + exact (mem_inv_normalize rsegs mem).
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
  - intros ms HQ.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & _).
    do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                    & m'' & HE & MU & WM & MI' & ja & jb & HS').
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    apply (SRcf_ret B).
    assert (MU' : munch [(spZ regs0 - stk, spZ regs0)] mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    assert (FR1 : lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A m' md).
    { eapply (lf_fr_evt B API SEGS AX HGG); [ exact FR | lia | lia | exact MU' | exact WM' | exact Hro' | ].
      intros x Hx0 NO. left.
      destruct (Z_le_dec (spZ regs0 - stk) x); destruct (Z_lt_dec x (spZ regs0)); try lia;
        exfalso; apply NO; cbn [Frame.outside]; (split; [ lia | exact I ]). }
    assert (Hrm : rw_cells rsegs m' r [CB 288 bs]).
    { apply (rw_cells_transport rsegs _ mem m' r _ Hr MU' WM').
      change (Z.of_nat (cells_size [CB 288 bs])) with 288. cbn [disjoint_from]. split; [ lia | exact I ]. }
    pose proof (bv_unsigned_in_range 8 vb) as R8. change (bv_modulus 8) with 256 in R8.
    exists (mkFP (@fp_regs fx') (@fp_csr fx')), regs', m', md, L, A, r, fab, ip, inn, bs, (bv_unsigned vb),
      j0, ja, jb.
    unfold llvm_regs_base. rewrite !(lf_getr_eqv _ _ _ Hx).
    split; [ rewrite SEGS; reflexivity | ].
    split; [ exact Hfrm | ].
    split.
    { split; [ exact E2 | ]. split; [ exact E3 | ]. split; [ exact E4 | ]. split; [ exact E8 | ].
      split; [ exact E22 | ]. split; [ exact E23 | ]. split; [ exact E24 | ]. split; [ exact E25 | ].
      split; [ exact E26 | exact E27 ]. }
    split; [ reflexivity | ]. split; [ exact H18 | ]. split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ reflexivity | ].
    split; [ exact (lf_rw_cells_rel m' m'' _ _ Hrel HS') | ].
    split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split; [ lia | ].
    split; [ exact Hrm | ]. split; [ exact Hinv | ]. split; [ exact Hfab | ].
    split; [ split; [ exact FR1 | split; [ exact Hmine | exact Hres ] ] | exact Hk1 ].
Qed.

End S.
