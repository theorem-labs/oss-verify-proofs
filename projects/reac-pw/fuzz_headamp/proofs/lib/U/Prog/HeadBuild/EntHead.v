(** The head of one ent_build turn in the UBSan image (0x134bc .. 0x1352c): memset(e, 0, 104), kind = fuzz_u8,
    kind % 10, and the dispatch (kind 9 by the branch to 0x1386c, kinds 0-8 by `jr a1` through the nine 4-byte
    offsets at 0x10520; an empty input to 0x13a20), given the case entries of EntFacts.v as premises. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

Section Head.
Variables (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MSET : memset_contract.
Hypothesis C0N : case0_nil_at sp gp tp s1 F fc m r src pp lo.
Hypothesis C0 : case_at sp gp tp s1 F fc m r src pp lo 0 0x13530.
Hypothesis C1 : case_at sp gp tp s1 F fc m r src pp lo 1 0x136c0.
Hypothesis C2 : case_at sp gp tp s1 F fc m r src pp lo 2 0x135ac.
Hypothesis C3 : case_at sp gp tp s1 F fc m r src pp lo 3 0x13614.
Hypothesis C4 : case_at sp gp tp s1 F fc m r src pp lo 4 0x1356c.
Hypothesis C5 : case_at sp gp tp s1 F fc m r src pp lo 5 0x1371c.
Hypothesis C6 : case_at sp gp tp s1 F fc m r src pp lo 6 0x137a8.
Hypothesis C7 : case_at sp gp tp s1 F fc m r src pp lo 7 0x13654.
Hypothesis C8 : case_at sp gp tp s1 F fc m r src pp lo 8 0x137ec.
Hypothesis C9 : case9_at sp gp tp s1 F fc m r src pp lo.

Lemma head_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
  evt rsegs (QJ sp gp tp s1 F fc m r src pp lo (ent_build r))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 (0xcccccccd * 2^32)) s4 (Z_to_bv 64 src) s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 95)
             (Z_to_bv 64 src) (Z_to_bv 64 4) t3 t4 t5 t6)
        F (Z_to_bv 64 ENT_HEAD) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6.
  pose proof (ep_range sp m r src pp lo HE) as R.
  destruct (ep_e_cells sp m r src pp lo HE) as (junk & LJ & CE).
  unfold ENT_HEAD.
  (* 0x134bc addi a0,sp,0xb8; addi a2,zero,0x68; mv a1,zero; jal memset *)
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
    { apply (munch_weaken [(bv_unsigned sp + 184, bv_unsigned sp + 184 + 104)] _ m m1); [|exact MU1].
      unfold sub_fp, WE, FRAME_LOCALS. cbn [outside]. intros x (O1 & O2 & _). split; [lia | exact I]. }
    split; [exact WM1|]. split; [exact MI1|].
    split; [apply (stk_after_call m m1 lo _ _ 104 (zeros 104) ST MU1 WM1 B1 eq_refl); exact (ep_rom sp m r src pp lo HE)|].
    split; [rewrite <- zeros104; exact B1 | reflexivity]. }
  clear MU1 WM1 MI1 B1 CE LJ junk.
  assert (Hr : r = [] \/ exists b rest, r = b :: rest) by (destruct r as [|b rest]; [left | right; eauto]; reflexivity).
  destruct Hr as [Er | (b & rest & Er)].
  - (* 0x134cc beqz s2: the input empty *)
    assert (L0 : length r = 0%nat) by (rewrite Er; reflexivity).
    step. brt.
    eapply C0N; [exact Er | exact MC].
  - assert (L0 : (0 < length r)%nat) by (rewrite Er; cbn; lia).
    step. brf.
    (* 0x134d0 addi s5,s10,1; addi a0,zero,1; bltu a0,s5,8 over the trap (taken) *)
    do 2 step. step. brt.
    (* 0x134e0 lbu a0,0(s10) *)
    pose proof (MemC_in_byte0 sp m r src pp lo HE _ _ _ _ MC L0) as HB0. rewrite Er in HB0. cbn [nth] in HB0.
    step.
    (* 0x134e4 .. 0x13504: kind % 10, s6 = |r| - 1, a2 = 8 *)
    do 9 step.
    match goal with |- context [Z_to_bv 64 (Z.land ?X 255)] =>
      replace (Z.land X 255) with (bv_unsigned b mod 10) by (symmetry; byte_eq b) end.
    pose proof (Z.mod_pos_bound (bv_unsigned b) 10 ltac:(lia)) as Hk.
    (* 0x13508 bltu a2,a1: kind 9 *)
    step.
    destruct (Z.eq_dec (bv_unsigned b mod 10) 9) as [K9|K9].
    + brt. eapply C9; [exact Er | exact K9 | exact MC].
    + brf.
      assert (Hs : forall s4' : word, s4' = Z_to_bv 64 (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 56)) ≫ 56) ->
                   (bv_signed s4' <? 0) = Z.testbit (bv_unsigned b) 7) by (intros s4' ->; byte_eq b).
      assert (Hc : bv_unsigned b mod 10 = 0 \/ bv_unsigned b mod 10 = 1 \/ bv_unsigned b mod 10 = 2 \/
                   bv_unsigned b mod 10 = 3 \/ bv_unsigned b mod 10 = 4 \/ bv_unsigned b mod 10 = 5 \/
                   bv_unsigned b mod 10 = 6 \/ bv_unsigned b mod 10 = 7 \/ bv_unsigned b mod 10 = 8) by lia.
      pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI1.
      destruct Hc as [K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]; rewrite K;
        (* 0x1350c slli; auipc; addi; add; lw; slli; add; srai; jr a1 *)
        do 9 step;
        ((lazymatch type of K with
          | _ = 0 => eapply C0 | _ = 1 => eapply C1 | _ = 2 => eapply C2 | _ = 3 => eapply C3 | _ = 4 => eapply C4
          | _ = 5 => eapply C5 | _ = 6 => eapply C6 | _ = 7 => eapply C7 | _ = 8 => eapply C8
          end);
         [exact Er | exact K | apply Hs; reflexivity | exact MC]).
Qed.

End Head.
