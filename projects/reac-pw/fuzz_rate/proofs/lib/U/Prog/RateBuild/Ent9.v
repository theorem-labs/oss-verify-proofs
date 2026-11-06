(** ent_build's kind 9 in the UBSan image (pod.h:366-376): a Struct holding the String "reac.cfg.rate". From the
    branch target 0x138a4 to the join 0x13ee4: the type, the String's size and type words, memcpy of the 14 bytes of
    s (0x1045e) into the body, the size 24, then 0x13a04 (s9 = s7) and 0x13a64 (s8, s11 reloaded from the cells
    sp + 0xd8 / 0xc8). The form is reac-pw/fuzz_role's U/Prog/RoleBuild/Ent9.v re-walked at rate's registers, cells
    and addresses. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts EntRo.
Import ListNotations.
Open Scope Z_scope.

Lemma s9_ok : rostr_ok 0x1045e S9 = true.
Proof. vm_compute. reflexivity. Qed.

Section Case9.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

Lemma case9_ok_sec : case9_at sp gp tp s3 F fc m r src pp lo.
Proof.
  intros ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 b rest m1 Er Hk MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (L : length r = S (length rest)) by (rewrite Er; reflexivity).
  (* 0x138a4 addi a0,zero,14; sw a0,0xe8(sp); sw a0,0xf0(sp) *)
  step. est_t HE MC. est_bd HE MC (bv_unsigned sp + 240) 0%nat 4%nat.
  (* 0x138b0 addi a0,sp,0xf0; addi a1,zero,-5; bltu a1,a0 (trap) *)
  do 2 step. step. brf.
  (* 0x138bc addi a0,zero,8; sw a0,0xf4(sp) *)
  step. est_bd HE MC (bv_unsigned sp + 244) 4%nat 4%nat.
  (* 0x138c4 addi a0,sp,0xf0; addi a1,zero,-9; bltu a1,a0 (trap) *)
  do 2 step. step. brf.
  (* 0x138d0 auipc; addi a1 = s; addi a2,zero,14; addi a0,sp,0xf8; jal memcpy *)
  do 5 step.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
  destruct (rostr_bytes _ 0x1045e S9 MI1 s9_ok) as (SB & _).
  assert (SB' := bytes_at_prefix _ _ (S9 ++ [NUL]) (img_slack 0x1045e S9) ltac:(rewrite <- app_assoc; exact SB)).
  destruct (MemC_cells sp m r src pp lo HE _ _ _ _ (bv_unsigned sp + 248) 14 MC ltac:(lia) ltac:(unfold FRAME_LOCALS; lia))
    as (junk & LJ & CJ).
  eapply evt_cut.
  { eapply MCPY with (src := S9 ++ [NUL]) (junk := junk).
    - rewrite unsigned_lit by lia. exact SB'.
    - rewrite unsigned_lit by lia. reflexivity.
    - rewrite !unsigned_lit by lia. exact CJ.
    - rewrite !unsigned_lit by lia.
      destruct (ro_apart sp m r src pp lo HE 0x1045e S9 (bv_unsigned sp + 248) 14 s9_ok ltac:(lia)
        ltac:(vm_compute; congruence) ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)); lia.
    - exact MI1. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mx &
              E & MU2 & WM2 & MI2 & CE2 & _).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU2, CE2 by lia.
  apply rw_CB_bytes in CE2 as [B2 _].
  pose proof (MemC_call_bd sp m r src pp lo HE _ mx _ _ _ _ 8 (S9 ++ [NUL]) MC MU2 WM2 MI2 B2 ltac:(lia)
    ltac:(apply Nat.leb_le; vm_compute; reflexivity)) as MC2.
  clear MC MU2 WM2 MI2 B2 MI1 SB SB' CJ. rename MC2 into MC.
  (* 0x138e4 addi a0,zero,24; sw a0,0xec(sp); mv t1,s8; j 0x13a04 *)
  step. est_sz HE MC. do 2 step.
  (* 0x13a04 mv s9,s7; j 0x13a64 *)
  do 2 step.
  (* 0x13a64 ld s8,0xd8(sp); ld s11,0xc8(sp); j 0x13ee4 *)
  pose proof (MemC_cd8 sp m r src pp lo HE _ _ _ _ MC) as HD8.
  pose proof (MemC_cc8 sp m r src pp lo HE _ _ _ _ MC) as HC8.
  do 3 step. clear HD8 HC8.
  eapply join_13ee4; [eb_tac Er Hk | | | exact MC | | | ].
  - f_equal. rewrite L. lia.
  - f_equal. rewrite L. lia.
  - apply le4_le32.
  - apply le4_le32.
  - vm_compute. reflexivity.
Qed.

End Case9.

Theorem case9_ok : forall (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte) (src pp lo : Z), ent_pre sp m r src pp lo -> memcpy_contract -> case9_at sp gp tp s3 F fc m r src pp lo.
Proof. intros. apply case9_ok_sec; assumption. Qed.
