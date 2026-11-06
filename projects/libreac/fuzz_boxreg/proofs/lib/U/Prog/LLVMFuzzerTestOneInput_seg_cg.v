(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/ZBridge.v; 287 of its 304 lines of code are new or changed and 392 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/U/Prog/LLVMFuzzerTestOneInput_seg.v; 9 of its 153 lines of code are new or changed and 160 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_top.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import LLVMFuzzerTestOneInput_seg LLVMFuzzerTestOneInput_cfb read_name_ccf LLVMFuzzerTestOneInput_top_cg.
Import ListNotations.
Open Scope Z_scope.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Lemma llvm_alloc_mem_cf : forall stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md r k mem' W,
  llvm_ctx_cf B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
  llvm_alloc B API stk L0 A0 regs0 mem0 md0 b L A mem md r k ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> spZ regs0 - stk <= x < spZ regs0 \/ r <= x < r + 288) ->
  llvm_alloc B API stk L0 A0 regs0 mem0 md0 b L A mem' md r k.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md r k mem' W CTX (FR & MINE & RES) MU WM Hro HW.
  pose proof CTX as (BI & Hk0 & _ & Hpre & _).
  pose proof BI as (SEGS & _ & _ & HGG & _ & AX).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & Hceil & H63 & _).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  unfold LLVM_K, LLVM_FRAME in Hk0.
  split; [|split; [exact MINE | exact RES]].
  eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | lia | lia | exact MU | exact WM | exact Hro |].
  intros x Hx NO. destruct (HW x Hx NO) as [H|H]; [left; exact H|].
  right. exists r, 288. split; [exact MINE | lia].
Qed.

Theorem llvm_case_of_evt_cf : forall op3, llvm_case_evt (llvm_case_pc op3) -> llvm_case_ok_cf B API op3.
Proof.
  intros op3 EV stk empty L0 A0 regs0 mem0 md0 ra p n b i k c CTX HT (ms & mdx & Ec & Epc).
  pose proof CTX as (BI & Hk0 & Hra & Hpre & Hsn & H47 & Hres0 & Hroom & Hro0 & Hgi & Hfrm0 & Hn26).
  pose proof BI as (SEGS & _ & _ & HGG & _ & AX).
  destruct HT as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & op & j0 & j1 & jm & Ec' & Hfrm & RB &
    E9 & E18 & E19 & E20 & E21 & FRC & Hi & Hinn & Hip & Hipn & Hop & RWR & INV & Hfab & AL & Hk).
  rewrite Ec' in Ec. injection Ec as Ems Emd. subst ms mdx. unfold YK11.mkst in Epc. cbn [ms_pc_val] in Epc.
  subst c. rewrite Epc.
  pose proof AL as (FR & MINE & RES).
  destruct RB as (E2 & E3 & E4 & E8 & E22 & E23 & E24 & E25 & E26 & E27).
  unfold LLVM_K, LLVM_FRAME in Hk0.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn1 & Hpl & Hrod).
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & Hro).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  pose proof INV as ((Lbs & B1 & _) & _).
  pose proof MINE as (Hin & _ & _).
  apply blocks_In in Hin as (q0 & Hq0 & Hq0in).
  pose proof (mr_blocks_aligned B _ (aa_laws API) L A mem md q0 288 HM Hq0in) as Hr16.
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q0 288 HM Hq0in) as Hrr.
  rewrite Hq0 in Hr16, Hrr.
  assert (Hpn : 4096 <= p /\ p + n <= spZ regs0 - stk).
  { destruct Hpl as [[En _] | [Hn (q & Hq & Hqp)]]; [lia|].
    destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 q n 0 HM0 Hq ltac:(lia)) as (_ & H1 & H2 & _).
    rewrite Hqp in H1, H2. lia. }
  assert (Hrimg : forall x, 0 <= x < 288 -> ~ in_img B (r + x)).
  { intros x Hx. destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + x) HM MINE ltac:(lia))
      as (_ & N & _). exact N. }
  assert (Hspa : (spZ regs0 - 464) mod 16 = 0).
  { replace (spZ regs0 - 464) with (spZ regs0 + (-29) * 16) by lia. rewrite Z.mod_add by lia. exact Hal. }
  destruct (sg_list mem (Z.to_nat (inn - 1)) (ip + 1) ltac:(lia) ltac:(lia)) as (rest & Hrest & Hpay).
  { intros x Hx. apply (llvm_payload_read_cf B API stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md x CTX FR).
    lia. }
  change (CB 8 j0 :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 fab) :: CB 8 j1 :: C8 (Z_to_bv 64 i) ::
          C8 (Z_to_bv 64 (bx_n bs)) :: CB 288 bs :: CB 8 jm :: C8 (Z_to_bv 64 (ip + 1)) ::
          C8 (Z_to_bv 64 (inn - 1)) :: llvm_saved_cells regs0)
    with ([CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1; C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (bx_n bs));
           CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (inn - 1))] ++ llvm_saved_cells regs0) in FRC.
  destruct (top_rwc_split mem _ _ _ FRC) as [FRP FRS].
  assert (E360 : Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1; C8 (Z_to_bv 64 i);
                                         C8 (Z_to_bv 64 (bx_n bs)); CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 (ip + 1));
                                         C8 (Z_to_bv 64 (inn - 1))]) = 360)
    by reflexivity.
  rewrite E360 in FRS.
  assert (FRPn : rw_cells rsegs (normalize rsegs mem) (spZ regs0 - 464)
    [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fab); CB 8 j1; C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (bx_n bs));
     CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 (ip + 1)); C8 (Z_to_bv 64 (inn - 1))]).
  { apply (lf_rw_cells_norm B); [exact SEGS | exact Hro | | exact FRP].
    rewrite E360. intros x Hx Himg'. pose proof (lf_in_img_top B _ SEGS Himg'). lia. }
  assert (RWRn : rw_cells rsegs (normalize rsegs mem) r [CB 288 bs]).
  { apply (lf_rw_cells_norm B); [exact SEGS | exact Hro | | exact RWR].
    change (Z.of_nat (cells_size [CB 288 bs])) with 288. exact Hrimg. }
  assert (STn : Frame.stk rsegs (normalize rsegs mem) (spZ regs0 - stk) (spZ regs0 - 464)).
  { apply lf_stk; [lia | lia |]. intros a Ha. unfold YP09.writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi'; pose proof (lf_in_img_top B a SEGS Hi'); lia).
    rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    rewrite <- SEGS. exact (Hstw a ltac:(lia)). }
  rewrite SEGS.
  eapply ((llvm_run_norm_cf B ltac:(segs_tac)) fx' regs _ mem md); [exact Hh | exact Hl | exact Hro | | |].
  - apply (EV (@fp_regs fx') (@fp_csr fx') regs (normalize rsegs mem) (spZ regs0 - 464) (spZ regs0 - stk) r fab
             ip inn op i (p + n) (getr regs0 3) (getr regs0 4) j0 j1 jm bs rest);
      first [ assumption | exact (mem_inv_normalize rsegs mem) | exact (bytes_at_normalize rsegs mem _ _ Hro Hpay)
            | lia ].
  - intros ms HQ.
    destruct HQ as (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' &
      s6' & s7' & t3' & t4' & t5' & t6' & m'' & j0' & j1' & jm' & q & cc & bs' & -> & _).
    do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' &
      s6' & s7' & t3' & t4' & t5' & t6' & m'' & j0' & j1' & jm' & q & cc & bs' & HE & E3' & E6' & E7' & MU & WM & MI &
      FRC' & Hq & Hc & Hqe & HB' & WR' & INV' & Hfab' & KEPT).
    injection HE as ER EF EP EC EM. subst R F pc' fc m''.
    rewrite MState.unsigned_lit in MU, FRC' by lia.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU)
      as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM)
      as WM'.
    pose proof (ro_agree_same rsegs mem m' Hro Hsame) as Hro'.
    assert (AL' : llvm_alloc B API stk L0 A0 regs0 mem0 md0 b L A m' md r k).
    { apply (llvm_alloc_mem_cf stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md r k m' _ CTX AL MU' WM' Hro').
      intros x Hx0 NO.
      destruct (Z_le_dec (spZ regs0 - stk) x); destruct (Z_lt_dec x (spZ regs0 - 464 + 360));
        destruct (Z_le_dec r x); destruct (Z_lt_dec x (r + 288)); try lia;
        exfalso; apply NO; cbn [outside]; repeat split; lia. }
    pose proof (rw_cells_transport rsegs _ mem m' _ _ FRS MU' WM') as FRS'.
    assert (FRS'' : rw_cells rsegs m' (spZ regs0 - 464 + 360) (llvm_saved_cells regs0)).
    { apply FRS'. unfold llvm_saved_cells. cbn [disjoint_from cells_size csize Nat.add].
      repeat split; lia. }
    pose proof (lf_rw_cells_rel m' m0' _ _ Hrel FRC') as FRC''.
    pose proof (top_rwc_join m' _ _ _ _ FRC'' ltac:(reflexivity) FRS'') as FRJ.
    pose proof (lf_rw_cells_rel m' m0' _ _ Hrel (sg_rw_mk m0' r bs' HB' (proj1 (proj1 INV')) WR')) as RWR'.
    apply (SRcf_ret B).
    exists k, (mkFP (@fp_regs fx') (@fp_csr fx')), regs', m', md, L, A, r, fab, q, cc, bs, bs', (-1), j0', j1', jm'.
    split; [rewrite SEGS; reflexivity|].
    split; [exact Hfrm|].
    split.
    { unfold llvm_regs_base. rewrite !(lf_getr_eqv _ _ _ Hx).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact E6'|]. split; [exact E7'|].
      split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
    split; [rewrite (lf_getr_eqv _ _ _ Hx); rewrite E3'; reflexivity|].
    split; [exact FRJ|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold boxreg_B1 in B1; lia|].
    split; [exact INV|]. split; [exact Hfab|].
    split; [exact RWR'|]. split; [exact INV'|]. split; [exact Hfab'|]. split; [exact KEPT|].
    split; [exact AL' | lia].
Qed.

End G.
