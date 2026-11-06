(** The head of one ent_build turn in the UBSan image (0x13560 .. 0x135d0): memset(e, 0, 104), kind = fuzz_u8,
    kind % 10, and the case switch (kind 9 by the branch at 0x135ac to 0x138a4, kinds 0-8 by `jr a1` at 0x135d0 through
    the nine 4-byte offsets at 0x10558; an empty input to 0x13ac4), given the case entries of EntFacts.v as premises.
    The form is reac-pw/fuzz_role's U/Prog/RoleBuild/EntHead.v at rate's registers. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** The jump table: the nine 4-byte words of the image at 0x10558, each a signed offset from 0x10558 (0x135b4
    `auipc a2`; 0x135b8 `addi a2,a2,-0x5c`; 0x135c0 `lw a1,0(a1)`; 0x135c8 `add a1,a1,a2`), give the targets of
    kinds 0-8. Checked on the image by computation; the walk below reads the same words by `step`. *)
Definition jt_word (k : nat) : Z :=
  match image_bytes rsegs (0x10558 + 4 * Z.of_nat k) 4 with
  | Some l => fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 l
  | None => -1
  end.

Lemma jt_targets :
  map (fun k => 0x10558 + (if jt_word k <? 2^31 then jt_word k else jt_word k - 2^32)) (seq 0 9)
  = [0x135d4; 0x13778; 0x13658; 0x136c0; 0x13610; 0x137d0; 0x137f4; 0x13708; 0x13830].
Proof. vm_compute. reflexivity. Qed.

Section Head.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MSET : memset_contract.
Hypothesis C0N : case0_nil_at sp gp tp s3 F fc m r src pp lo.
Hypothesis C0 : case_at sp gp tp s3 F fc m r src pp lo 0 0x135d4.
Hypothesis C1 : case_at sp gp tp s3 F fc m r src pp lo 1 0x13778.
Hypothesis C2 : case_at sp gp tp s3 F fc m r src pp lo 2 0x13658.
Hypothesis C3 : case_at sp gp tp s3 F fc m r src pp lo 3 0x136c0.
Hypothesis C4 : case_at sp gp tp s3 F fc m r src pp lo 4 0x13610.
Hypothesis C5 : case_at sp gp tp s3 F fc m r src pp lo 5 0x137d0.
Hypothesis C6 : case_at sp gp tp s3 F fc m r src pp lo 6 0x137f4.
Hypothesis C7 : case_at sp gp tp s3 F fc m r src pp lo 7 0x13708.
Hypothesis C8 : case_at sp gp tp s3 F fc m r src pp lo 8 0x13830.
Hypothesis C9 : case9_at sp gp tp s3 F fc m r src pp lo.

Lemma head_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s11 t3 t4 t5 t6 : word),
  evt rsegs (QJ sp gp tp s3 F fc m r src pp lo (ent_build r))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x188)) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 95) s3 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 10) (Z_to_bv 64 0x4000) s7 s8
             (Z_to_bv 64 src) (Z_to_bv 64 (Z.of_nat (length r))) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ENT_HEAD) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s11 t3 t4 t5 t6.
  pose proof (ep_range sp m r src pp lo HE) as R.
  destruct (ep_e_cells sp m r src pp lo HE) as (junk & LJ & CE).
  unfold ENT_HEAD.
  (* 0x13560 addi a0,sp,0xe8; addi a2,zero,0x68; mv a1,zero; jal memset *)
  do 4 step.
  eapply evt_cut.
  { eapply MSET with (junk := junk). { rewrite !unsigned_lit by lia. exact CE. } exact (ep_mem_inv sp m r src pp lo HE). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              E & MU1 & WM1 & MI1 & CE1).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU1, CE1 by lia.
  replace (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 104)) with (zeros 104) in CE1 by (vm_compute; reflexivity).
  apply rw_CB_bytes in CE1 as [B1 _].
  assert (MC : MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96)).
  { pose proof (ep_stk sp m r src pp lo HE) as ST.
    split.
    { apply (munch_weaken [(bv_unsigned sp + 232, bv_unsigned sp + 232 + 104)] _ m m1); [|exact MU1].
      unfold sub_fp, WE, FRAME_LOCALS. cbn [outside]. intros x (O1 & O2 & O3 & _). split; [lia | exact I]. }
    split; [exact WM1|]. split; [exact MI1|].
    split; [apply (stk_after_call m m1 lo _ _ 104 (zeros 104) ST MU1 WM1 B1 eq_refl); exact (ep_rom sp m r src pp lo HE)|].
    split; [rewrite <- zeros104; exact B1 | reflexivity]. }
  clear MU1 WM1 MI1 B1 CE LJ junk.
  assert (Hr : r = [] \/ exists b rest, r = b :: rest) by (destruct r as [|b rest]; [left | right; eauto]; reflexivity).
  destruct Hr as [Er | (b & rest & Er)].
  - (* 0x13570 beqz s10: the input empty *)
    assert (L0 : length r = 0%nat) by (rewrite Er; reflexivity).
    step. brt.
    eapply C0N; [exact Er | exact MC].
  - assert (L0 : (0 < length r)%nat) by (rewrite Er; cbn; lia).
    step. brf.
    (* 0x13574 addi s7,s9,1; addi a0,zero,1; bltu a0,s7 (taken: past the trap at 0x13580) *)
    do 2 step. step. brt.
    (* 0x13584 mv t1,s10; 0x13588 lbu a0,0(s9) *)
    step.
    pose proof (MemC_in_byte0 sp m r src pp lo HE _ _ _ _ MC L0) as HB0. rewrite Er in HB0. cbn [nth] in HB0.
    step.
    (* 0x1358c .. 0x135a8: kind % 10 (the multiplier 0xcd, s5 = 10), s8 = |r| - 1, a2 = 8 *)
    do 8 step.
    match goal with |- context [Z_to_bv 64 (Z.land ?X 255)] =>
      replace (Z.land X 255) with (bv_unsigned b mod 10) by (symmetry; byte_eq b) end.
    pose proof (Z.mod_pos_bound (bv_unsigned b) 10 ltac:(lia)) as Hk.
    (* 0x135ac bltu a2,a1: kind 9 *)
    step.
    destruct (Z.eq_dec (bv_unsigned b mod 10) 9) as [K9|K9].
    + brt. eapply C9; [exact Er | exact K9 | exact MC].
    + brf.
      assert (Hs : forall s11' : word, s11' = Z_to_bv 64 (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 56)) ≫ 56) ->
                   (bv_signed s11' <? 0) = Z.testbit (bv_unsigned b) 7) by (intros s11' ->; byte_eq b).
      assert (Hc : bv_unsigned b mod 10 = 0 \/ bv_unsigned b mod 10 = 1 \/ bv_unsigned b mod 10 = 2 \/
                   bv_unsigned b mod 10 = 3 \/ bv_unsigned b mod 10 = 4 \/ bv_unsigned b mod 10 = 5 \/
                   bv_unsigned b mod 10 = 6 \/ bv_unsigned b mod 10 = 7 \/ bv_unsigned b mod 10 = 8) by lia.
      pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
      destruct Hc as [K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]; rewrite K;
        (* 0x135b0 slli; auipc; addi; add; lw; slli; add; srai; jr a1 *)
        do 9 step;
        ((lazymatch type of K with
          | _ = 0 => eapply C0 | _ = 1 => eapply C1 | _ = 2 => eapply C2 | _ = 3 => eapply C3 | _ = 4 => eapply C4
          | _ = 5 => eapply C5 | _ = 6 => eapply C6 | _ = 7 => eapply C7 | _ = 8 => eapply C8
          end);
         [exact Er | exact K | apply Hs; reflexivity | exact MC]).
Qed.

End Head.
