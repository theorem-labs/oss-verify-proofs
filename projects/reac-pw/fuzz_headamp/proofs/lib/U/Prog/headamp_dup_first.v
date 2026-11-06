(** headamp_dup_first_contract (U/Prog/LLVMFuzzerTestOneInput_c.v), [0x147e0, 0x147fc) of the UBSan image:
    first = fuzz_dup(out, 3 max(rc, 0)) past its malloc (fuzz.h:75-78). 0x147e0 `beqz a0` not taken (first <> 0),
    0x147e4 `mv s7,a0`, 0x147e8 `blez s6`: for rc <= 0 straight to 0x147fc; for rc > 0 `mv a0,s7; mv a1,s3;
    mv a2,s8` and memcpy(first, out, 3 rc) at 0x147f8 (ra 0x147fc) by U/Prog/memcpy_c.v's contract, whose post
    leaves first = the 3 rc bytes of out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c EvtFacts.
Import ListNotations.
Open Scope Z_scope.

Theorem headamp_dup_first_holds : memcpy_c.memcpy_contract -> headamp_dup_first_contract.
Proof.
  intros MCPY. unfold headamp_dup_first_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    w junk rc out first -> Hf0 -> -> Hrc -> HW HFC HSEP HMI.
  assert (HQ : 1 <= first_req rc) by (unfold first_req; destruct (Z.ltb_spec 0 rc); lia).
  destruct (rw_cells_bound rsegs m first _ HFC) as [HF0 HF1]. cbn [cells_size csize] in HF1.
  rewrite Nat.add_0_r, Z2Nat.id in HF1 by lia.
  unfold HEAD_DUP_FIRST, HEAD_PLAIN.
  (* 0x147e0 beqz a0 *)
  step. rewrite eqb_u by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv beta iota.
  (* 0x147e4 mv s7,a0; 0x147e8 blez s6 *)
  step. step. rewrite lts_s by lia.
  destruct (Z.ltb_spec 0 rc) as [Hp|Hn]; cbn [negb]; cbv beta iota.
  2:{ (* rc <= 0: nothing copied *)
      apply evt_done. do 16 eexists. exists m. split; [reflexivity|].
      split; [intros H; exfalso; lia|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact HMI]. }
  destruct (HW Hp) as [HWL HWB]. destruct (bytes_at_bound rsegs m out w HWB) as [HO0 HO1].
  assert (EQ : first_req rc = 3 * rc) by (unfold first_req; rewrite (proj2 (Z.ltb_lt 0 rc) Hp); reflexivity).
  assert (EM : Z.max rc 0 = rc) by lia.
  rewrite EQ in HFC, HSEP. rewrite EM in HSEP |- *.
  (* 0x147ec mv a0,s7; mv a1,s3; mv a2,s8; jal memcpy *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MCPY with (src := w) (junk := junk).
    - rewrite unsigned_lit by lia. exact HWB.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. exact HFC.
    - rewrite !unsigned_lit by lia. lia.
    - exact HMI. }
  intros ms' Hpost. unfold memcpy_c.memcpy_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                     E & MU1 & WM1 & MI1 & CB1 & _).
  subst ms'. rewrite !unsigned_lit in MU1, CB1 by lia. ret_even.
  apply evt_done. do 16 eexists. exists m1. split; [reflexivity|].
  split; [intros _; exact (rw_cells_CB_bytes m1 first _ _ CB1)|].
  split; [rewrite EQ; exact MU1|]. split; [exact WM1 | exact MI1].
Qed.
