From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09 YO05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract OutForm Img0.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr FP.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel KindB fread_c fread_ro_c memmove_c memmove_ro_c
  rd_u32_c pcap_source_struct pcap_source_struct_next pcap_lib pcap_source_next_lib
  pcap_source_next_ep pcap_source_next_c pcap_source_next_loop.
Import ListNotations YK11.
Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState}.

Theorem pcap_source_next_holds : fread_ro_contract -> memmove_ro_contract -> rd_u32_contract ->
  pcap_source_next_contract.
Proof.
  intros HFR HMM HRD. unfold pcap_source_next_contract.
  intros regs mem md ps buf cap ts h swz b p fl mdv lo lol lvt lvid pv nx tsv pad bj Fc
    A0 A1 A2 A3 HRA SPS PNZ PAL HPS HH HNZ HCAP HB4K HBJ HBN HIB HBL2 HTS HG1 HG2 EF GU RO ST LO HLO SPB FR Hh Hl FD.
  unfold NEXT_K, spZ in *.
  pose proof (zr_word (getr regs 2)) as Rsp. unfold inr64 in Rsp.
  pose proof (rw_cells_bound rsegs _ _ _ HPS) as HPR. cbn [cells_size csize ps_cells Nat.add] in HPR.
  pose proof (u8arr_len _ _ _ HBJ) as HBR.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (TSD : ts = 0 \/ bv_unsigned (getr regs 2) <= ts)
    by (destruct (Z.eq_dec ts 0) as [T|T]; [left; exact T | right; exact (proj1 (HTS T))]).
  assert (HTR : 0 <= ts < 2 ^ 64).
  { destruct (Z.eq_dec ts 0) as [T|T]; [lia|]. destruct (HTS T) as (T1 & _ & _ & C).
    pose proof (rw_cells_bound rsegs _ _ _ C) as CB. cbn [cells_size csize Nat.add] in CB. lia. }
  hide_hyp HTS. hide_hyp HNZ. hide_hyp HIB.
  assert (UPS : bv_unsigned (wz ps) = ps) by (apply unsigned_lit; lia).
  assert (X0 : Regs6ss.xregs_eqv regs (mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
            (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (wz ps) (wz buf) (wz cap) (wz ts) (getr regs 14)
            (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
            (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
            (getr regs 29) (getr regs 30) (getr regs 31)))
    by (apply Regs6ss.mkR_eqv_of; first [reflexivity | exact A0 | exact A1 | exact A2 | exact A3]).
  eapply psn_evt_SRO; [exact (eqv_mk fx _ regs _ mem _ (Regs6ss.xregs_eqv_sym _ _ X0)) | | exact Hh | exact Hl |].
  { eapply (psn_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@YK11.fp_regs fx) (@YK11.fp_csr fx)
              mem lo h swz lol lvt lvid pad).
    - exact ST.
    - lia.
    - exact HLO.
    - rewrite UPS. exact SPS.
    - rewrite UPS. exact PNZ.
    - rewrite UPS. exact PAL.
    - rewrite UPS. exact HPS.
    - exact HH. }
  intros can ms' (m1 & MU1 & WM1 & ST1 & [(H0 & STE & ->) | (H0 & sp' & ph & SP' & FA & FB & FC & x0 & ->)]) EQ1.
  - subst h.
    destruct (psn_eg _ _ _ _ _ EF GU MU1 WM1 ltac:(unfold A_STDERR; disj_tac) ltac:(unfold A_GOT_GUARD; disj_tac)
                ltac:(unfold A_GUARD; disj_tac)) as [EF1 GU1].
    unfold psn_out. rewrite Z.eqb_refl. cbv beta iota.
    apply SRO_ret.
    destruct (@eqv_mkst fx _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R' & -> & X').
    exists R', m1, (@YK11.fp_regs fx), (@YK11.fp_csr fx), mdv.
    split; [rewrite (ret_pc_of_ok _ HRA); reflexivity|].
    split; [exact FR|]. split; [intros k _; reflexivity|].
    split; [exact (psn_preserved regs R' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X')|].
    split; [clear - MU1; eapply munch_weaken; [| exact MU1]; unfold sub_fp; out_tac|].
    split; [exact WM1|]. split; [exact EF1|]. split; [exact GU1|].
    split; [exact (ro_agree_munch_apart _ _ _ RO MU1 ltac:(ro_tac))|].
    split; [exact STE|].
    split; [intros _; split; [exact (getr_of_eqv _ _ 10 X' eq_refl) |
                              clear - MU1; eapply munch_weaken; [| exact MU1]; unfold sub_fp; out_tac]|].
    intros C. exfalso. apply C. reflexivity.
  - destruct (HNZ H0) as (HMS & HSW & HN26 & HHL & HBL & HIH & HBH & HBB & HBI).
    hide_hyp HSW. hide_hyp HBH. hide_hyp HBB. hide_hyp HBI.
    pose proof (psn_mstl_q _ _ _ _ _ _ _ HMS) as ((HQ0 & HQ1) & HH0 & HB0).
    destruct (psn_eg _ _ _ _ _ EF GU MU1 WM1 ltac:(unfold A_STDERR; disj_tac) ltac:(unfold A_GOT_GUARD; disj_tac)
                ltac:(unfold A_GUARD; disj_tac)) as [EF1 GU1].
    assert (RO1 : MemNorm.ro_agree rsegs m1) by exact (ro_agree_munch_apart _ _ _ RO MU1 ltac:(ro_tac)).
    assert (HTS1 : ts <> 0 -> bv_unsigned (getr regs 2) <= ts /\ ts mod 8 = 0 /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\
                              rw_cells rsegs m1 ts [C8 tsv]).
    { intros T. destruct (HTS T) as (T1 & T2 & T3 & C). split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
      exact (rw_cells_transport rsegs _ _ _ _ _ C MU1 WM1 ltac:(disj_tac)). }
    hide_hyp HTS1.
    unfold ps_cells in HPS.
    xp_rw HPS MU1 WM1. xp_mstl HMS MU1 WM1. xp_u8 HBJ MU1 WM1.
    rewrite <- SP' in FA, FB, FC.
    unfold psn_out. rewrite (proj2 (Z.eqb_neq h 0) H0). cbv beta iota. unfold psn_chain.
    eapply SRO_mono.
    { exact (psn_loop HFR HMM HRD (S (length Fc)) regs (@YK11.fp_regs fx) md (swz =? 1) Fc cap ps buf ts h swz b lo fl
               lol lvt lvid pv nx tsv pad
               (getr regs 1) sp' (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
               (wz (bv_unsigned sp' + 8)) (wz buf) x0 (wz buf) (wz cap) (wz h) (wz ts) (getr regs 15) (getr regs 16)
               (getr regs 17) (wz ps) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (wz cap)
               (wz (bv_unsigned sp' + 16)) (wz (-4)) (wz 16) (wz (bv_unsigned sp' + 12))
               (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
               (@YK11.fp_regs fx) (@YK11.fp_csr fx) m1 ms' p None bj ph mdv
               ltac:(lia) EQ1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
               eq_refl eq_refl ltac:(unfold spZ; lia) FA FB FC
               ltac:(rewrite SP'; exact ST1) ltac:(lia) HLO ltac:(unfold spZ; lia) HPS HSW HMS HIH HHL HBL HN26 HCAP HB4K
               HBJ HBN HIB HBL2 HBH HBB HBI HTS1 HTR EF1 GU1 RO1 FR ltac:(intros k _; reflexivity) Hh Hl). }
    intros c' (R' & m' & Ft & fc' & mdv' & -> & FR' & FA' & PR' & G10 & MU' & WM' & EF' & GU' & RO' & ST' & RES).
    exists R', m', Ft, fc', mdv'.
    split; [rewrite (ret_pc_of_ok _ HRA); reflexivity|].
    split; [exact FR'|]. split; [exact FA'|]. split; [exact PR'|].
    split.
    { unfold psn_W, NEXT_K, spZ in MU'. eapply munch_trans; [| exact MU'].
      clear - MU1. eapply munch_weaken; [| exact MU1]. unfold sub_fp. out_tac. }
    split; [exact (wmono_trans rsegs _ _ _ WM1 WM')|]. split; [exact EF'|]. split; [exact GU'|]. split; [exact RO'|].
    split; [exact ST'|].
    split; [intros C; exfalso; exact (H0 C)|].
    intros _. unfold psn_open_post, psn_q, psn_lh, psn_chain.
    destruct RES as (MS' & PS' & (bj' & HBJ' & LB' & FB') & TS').
    split; [exact G10|]. split; [exact MS'|]. split; [exact PS'|].
    split; [exists bj'; split; [exact HBJ'|]; split; [apply Nat2Z.inj; lia | exact FB']|]. exact TS'.
Qed.

End K.
