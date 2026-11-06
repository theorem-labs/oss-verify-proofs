(* fprintf (musl src/stdio/fprintf.c; plain 0x196fc, 100 bytes), PLAIN build, on link's memory FILE:
   `fprintf_contract` (lib/Prog/fprintf_c.v) from `vfprintf_contract` (lib/Prog/vfprintf_c.v).

   The walk is the shape of libpcap/fuzz_pcap lib/E2/S3/F_printf_core__S3.v Section FprintfFile
   (ossv/recipes 4b6f0df50aa; the code of fprintf is the same in both images: ident_wide.py
   libpcap/fuzz_pcap plain fprintf, "instructions 25 ... IDENTICAL"), restated in lib/Lib's vocabulary over
   `mkR` and closed with `leaf_fp_intro` (lib/Prog/mk_leaf_fp.v). `step` reads each instruction from the
   image the proof loads (rsegs); no instruction list is written here.

   The 24 instructions the walk runs:
   +0x00 addi sp,sp,-0x50; +0x04 sd ra,0x18(sp); +0x08 sd s0,0x10(sp); +0x0c sd a6,0x40(sp);
   +0x10 sd a7,0x48(sp); +0x14 auipc a6,7; +0x18 ld s0,0x1c8(a6) (the GOT slot 0x208d8: &guard 0x95878);
   +0x1c sd a2,0x20(sp); +0x20 sd a3,0x28(sp); +0x24 sd a4,0x30(sp); +0x28 sd a5,0x38(sp);
   +0x2c ld a2,0(s0) (the guard); +0x30 addi a3,sp,0x20; +0x34 sd a2,8(sp); +0x38 sd a3,0(sp);
   +0x3c addi a2,sp,0x20 (the va_list: the six slots a2..a7 at sp+0x20); +0x40 jal vfprintf;
   +0x44 ld a1,0(s0); +0x48 ld a2,8(sp); +0x4c bne a1,a2 (not taken: vfprintf writes neither the guard
   nor fprintf's frame); +0x50 ld ra,0x18(sp); +0x54 ld s0,0x10(sp); +0x58 addi sp,sp,0x50; +0x5c ret.

   The call is vfprintf's contract at the register map after the stores (sp' = sp - 80, a2 = sp - 48,
   a0 / a1 unchanged); its Pre is fprintf's carried over the 80 bytes of fprintf's own frame (the FILE
   block, the format, the strings, the GOT slot and the guard all lie outside [sp - 80, sp)).
   The call kit (q_ext, evt_canon, leaf_fp_q_ext, canon_of_preserved, leaf_fp_call) comes from
   lib/Prog/mk_call.v and the memory-frame lemmas (munch_mbyte, val_munch, bytes_munch, memfile_at_munch) from
   lib/Prog/mf_walk.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c printf_facts_c
  vfprintf_c fprintf_c mk_leaf mk_leaf_fp mk_call mf_walk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YH02 YI04 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

(* ==========================================================================
   1. fprintf's frame [S - 80, S): what vfprintf's Pre reads is outside it
   ========================================================================== *)

Lemma out_frame : forall S z, ~ (S + -80 <= z < S) -> outside [(S + -80, S)] z.
Proof. intros S z H. cbn [outside]. split; [exact H | exact I]. Qed.

Lemma val_out : forall m0 m1 S a n v, YI04.val_mem rsegs m0 a n v -> munch [(S + -80, S)] m0 m1 ->
  0 <= a -> a + Z.of_nat n <= S + -80 -> S <= 2 ^ 64 -> YI04.val_mem rsegs m1 a n v.
Proof.
  intros m0 m1 S a n v H MU H0 H1 HS. eapply val_munch; [exact H | exact MU | lia | lia |].
  intros z Hz. apply out_frame. lia.
Qed.

Ltac nat_lits := cbn [Z.of_nat Pos.of_succ_nat Pos.succ].

Lemma memfile_k_move : forall m0 m1 S f k, memfile_k m0 f k -> munch [(S + -80, S)] m0 m1 -> wmono rsegs m0 m1 ->
  f + MemFile.MF_BLOCK <= S + -80 -> S <= 2 ^ 64 -> memfile_k m1 f k.
Proof.
  intros m0 m1 S f k (HA & HW & W1 & W2 & HP) MU WM HB HS.
  pose proof HA as (Hf0 & Hf1 & _).
  split; [|split; [|split; [|split]]].
  - eapply memfile_at_munch; [exact HA | exact MU |]. intros z Hz. apply out_frame.
    unfold MemFile.MF_ZEROED, MemFile.MF_BLOCK in *. lia.
  - unfold mf_win, mf_fld in *. unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *.
    destruct HW as [(Hk & H1 & H2 & H3) | (Hk & H1 & H2 & H3)]; [left | right];
      (split; [exact Hk|]);
      (split; [|split]); (eapply val_out; [eassumption | exact MU | lia | nat_lits; lia | exact HS]).
  - exact (wr_at_transport _ _ _ _ _ W1 WM).
  - exact (wr_at_transport _ _ _ _ _ W2 WM).
  - exact HP.
Qed.

Lemma mf_dyn_move : forall m0 m1 S f fl om wend wpos wbase pos len,
  mf_dyn m0 f fl om wend wpos wbase pos len -> munch [(S + -80, S)] m0 m1 ->
  0 <= f -> f + MemFile.MF_BLOCK <= S + -80 -> S <= 2 ^ 64 -> mf_dyn m1 f fl om wend wpos wbase pos len.
Proof.
  intros m0 m1 S f fl om wend wpos wbase pos len
    (R1 & R2 & R3 & R4 & R5 & R6 & R7 & H1 & H2 & H3 & H4 & H5 & H6 & H7) MU H0 HB HS.
  unfold mf_dyn, mf_fld, MemFile.MF_COOKIE, MemFile.MF_BLOCK in *.
  refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 _))))))).
  repeat split; (eapply val_out; [eassumption | exact MU | lia | nat_lits; lia | exact HS]).
Qed.

Lemma args_move : forall m0 m1 S lo D n ws args,
  pf_args_ok m0 S lo D n ws args -> munch [(S + -80, S)] m0 m1 -> lo <= S + -80 ->
  pf_args_ok m1 (S + -80) lo D n ws args.
Proof.
  intros m0 m1 S lo D n ws args. revert ws.
  induction args as [|a args IH]; intros ws H MU HL; [destruct ws; exact I|].
  destruct ws as [|r ws]; [destruct H|]. destruct H as [H1 H2]. split; [|exact (IH ws H2 MU HL)].
  destruct a as [v|u|s]; cbn [pf_arg_ok] in *; try exact H1.
  destruct H1 as [HF [slack (BY & PAD & POS & L1 & L2)]].
  split; [exact HF|]. exists slack.
  split; [|split; [exact PAD|split; [exact POS|split; [lia|exact L2]]]].
  apply (bytes_munch _ m0 m1 _ _ BY MU).
  intros z Hz. apply out_frame.
  unfold pf_bytes in Hz. rewrite length_app, length_map, length_app in Hz. cbn [length] in Hz. lia.
Qed.

Lemma guard_move : forall m0 m1 S, guard_words m0 -> munch [(S + -80, S)] m0 m1 ->
  GUARD + 8 <= S + -80 -> guard_words m1.
Proof.
  intros m0 m1 S (HG & g & HQ) MU HB. split.
  - apply (bytes_munch _ m0 m1 _ _ HG MU). rewrite length_le8. intros z Hz. apply out_frame.
    unfold GOT_GUARD, GUARD in *. lia.
  - exists g. apply (bytes_munch _ m0 m1 _ _ HQ MU). rewrite length_le8. intros z Hz. apply out_frame. lia.
Qed.

(* vfprintf's Pre at the call, from fprintf's at entry *)
Lemma vf_pre_intro : forall (R : bvmap 5 word) (m0 m1 : word -> option byte) (S : Z)
    (f k fl om wend wpos wbase pos len : Z) (pb : list byte)
    (fmt : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z) (ws : list word),
  arg R 0 = f -> arg R 2 = S - 48 -> spZ R = S - 80 -> length ws = 6%nat -> S < 2 ^ 63 ->
  memfile_k m0 f k -> mf_dyn m0 f fl om wend wpos wbase pos len ->
  mf_pend_bytes m0 f pb -> Z.of_nat (length pb) = k ->
  bytes_at rsegs m0 (arg R 1) (pf_bytes (fmt ++ [0])) ->
  RO_LO <= arg R 1 -> arg R 1 + Z.of_nat (length fmt) + 1 <= RO_END ->
  pf_parse fmt = Some ps -> pf_text ps args = Some T ->
  pf_args_ok m0 S (S - FPRINTF_K) f MemFile.MF_BLOCK ws args ->
  k + Z.of_nat (length T) <= MemFile.MF_BUFSIZ ->
  f + MemFile.MF_BLOCK <= S - FPRINTF_K -> IMG_TOP <= S - FPRINTF_K ->
  guard_words m0 ->
  munch [(S + -80, S)] m0 m1 -> wmono rsegs m0 m1 -> va_slots m1 (S - 48) ws ->
  arg R 0 = f /\
  memfile_k m1 f k /\ mf_dyn m1 f fl om wend wpos wbase pos len /\
  mf_pend_bytes m1 f pb /\ Z.of_nat (length pb) = k /\
  bytes_at rsegs m1 (arg R 1) (pf_bytes (fmt ++ [0])) /\
  RO_LO <= arg R 1 /\ arg R 1 + Z.of_nat (length fmt) + 1 <= RO_END /\
  pf_parse fmt = Some ps /\ pf_text ps args = Some T /\
  va_slots m1 (arg R 2) ws /\ spZ R <= arg R 2 /\
  arg R 2 + 8 * Z.of_nat (length ws) <= 2 ^ 63 /\
  pf_args_ok m1 (spZ R) (spZ R - VFPRINTF_K) f MemFile.MF_BLOCK ws args /\
  k + Z.of_nat (length T) <= MemFile.MF_BUFSIZ /\
  f + MemFile.MF_BLOCK <= spZ R - VFPRINTF_K /\ IMG_TOP <= spZ R - VFPRINTF_K /\
  guard_words m1.
Proof.
  intros R m0 m1 S f k fl om wend wpos wbase pos len pb fmt ps args T ws
    HA0 HA2 HSP HL HS HMK HDY HPB HK HFMT HR1 HR2 HPS HTX HPA HFIT HBLK HIMG HGW MU WM HVA.
  pose proof (memfile_k_range _ _ _ HMK) as Hk.
  pose proof (memfile_k_at _ _ _ HMK) as (Hf0 & Hf1 & _).
  unfold FPRINTF_K, VFPRINTF_K, IMG_TOP, RO_LO, RO_END in *.
  rewrite HA2, HSP, HL. change (Z.of_nat 6) with 6.
  refine (conj HA0 (conj _ (conj _ (conj _ (conj HK (conj _ (conj HR1 (conj HR2 (conj HPS (conj HTX
    (conj HVA (conj _ (conj _ (conj _ (conj HFIT (conj _ (conj _ _))))))))))))))))).
  - eapply memfile_k_move; [exact HMK | exact MU | exact WM | unfold MemFile.MF_BLOCK in *; lia | lia].
  - eapply mf_dyn_move; [exact HDY | exact MU | lia | unfold MemFile.MF_BLOCK in *; lia | lia].
  - unfold mf_pend_bytes in *. eapply bytes_munch; [exact HPB | exact MU |].
    intros z Hz. apply out_frame. unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *. lia.
  - eapply bytes_munch; [exact HFMT | exact MU |].
    intros z Hz. apply out_frame. unfold pf_bytes in Hz. rewrite length_map, length_app in Hz.
    cbn [length] in Hz. lia.
  - lia.
  - lia.
  - replace (S - 80 - 5968) with (S - 6048) by lia. replace (S - 80) with (S + -80) by lia.
    eapply args_move; [exact HPA | exact MU | lia].
  - lia.
  - lia.
  - eapply guard_move; [exact HGW | exact MU | unfold GUARD; lia].
Qed.

(* the Post of vfprintf and of fprintf (the same text) reads the result register only *)
Lemma pf_post_ext : forall f k pb T fl om wend pos len,
  post_ext (fun (regs : bvmap 5 word) (m : word -> option byte) (regs' : bvmap 5 word) (m' : word -> option byte) =>
    res regs' = Z.of_nat (length T) /\ pf_file_post m' f k pb T fl om wend pos len).
Proof.
  intros f k pb T fl om wend pos len r1 r2 m q1 q2 m' _ E H. unfold getr_same in E. cbv beta in *.
  unfold res in *. rewrite <- E. exact H.
Qed.

(* ==========================================================================
   2. Facts the walk uses
   ========================================================================== *)

Definition fp_hold (P : Prop) : Prop := P.
Lemma fp_hide : forall P : Prop, P -> fp_hold P. Proof. intros P H. exact H. Qed.

Lemma fp_ro_c8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

(* the six argument slots fprintf stores at sp + 0x20 .. + 0x48 are vfprintf's va_list *)
Lemma fr_slots : forall m A B x0 x1 x2 x3 w2 w3 w4 w5 w6 w7,
  rw_cells rsegs m A [C8 x0; C8 x1; C8 x2; C8 x3; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7] ->
  B = A + 32 -> va_slots m B [w2; w3; w4; w5; w6; w7].
Proof.
  intros m A B x0 x1 x2 x3 w2 w3 w4 w5 w6 w7 [[_ HB] _] ->.
  cbn [cells_bytes cbytes] in HB. unfold va_slots. cbn [flat_map].
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [_ HB]. rewrite length_le8 in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [_ HB]. rewrite length_le8 in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [_ HB]. rewrite length_le8 in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [_ HB]. rewrite length_le8 in HB.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in HB.
  replace (A + 32) with (A + 8 + 8 + 8 + 8) by lia. exact HB.
Qed.

(* every byte of the stack window is in the image or below TASK_SIZE *)
Lemma stk_task : forall m lo hi x, task_mem rsegs m -> stk rsegs m lo hi -> lo <= x < hi ->
  find_segment rsegs x 1 <> None \/ x < TASK_SIZE.
Proof.
  intros m lo hi x TM (H0 & H1 & H) Hx. destruct (H x Hx) as [_ [b Hb]].
  assert (E : bv_unsigned (wa x) = x) by (apply wa_unsigned; lia).
  unfold mrd in Hb. destruct (m (wa x)) as [b'|] eqn:Em.
  - pose proof (TM _ _ Em) as T. rewrite E in T. exact T.
  - left. unfold seg_rom, memory_read in Hb. change (Z.of_N 1) with 1 in Hb. rewrite E in Hb.
    destruct (find_segment rsegs x 1) as [sg|]; [discriminate | discriminate Hb].
Qed.

Lemma task_mem_munch : forall m m' a b, task_mem rsegs m -> munch [(a, b)] m m' ->
  (forall x, a <= x < b -> find_segment rsegs x 1 <> None \/ x < TASK_SIZE) -> task_mem rsegs m'.
Proof.
  intros m m' a b TM MU HX x bx E.
  destruct (Z.leb_spec a (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) b).
  - apply HX. lia.
  - rewrite (MU x) in E by (cbn [outside]; split; [lia | exact I]). exact (TM x bx E).
  - rewrite (MU x) in E by (cbn [outside]; split; [lia | exact I]). exact (TM x bx E).
  - rewrite (MU x) in E by (cbn [outside]; split; [lia | exact I]). exact (TM x bx E).
Qed.

Lemma munch_join : forall W1 W2 W m0 m1 m2, munch W1 m0 m1 -> munch W2 m1 m2 ->
  sub_fp W1 W -> sub_fp W2 W -> munch W m0 m2.
Proof.
  intros W1 W2 W m0 m1 m2 H1 H2 S1 S2. eapply munch_trans.
  - exact (munch_weaken W1 W m0 m1 S1 H1).
  - exact (munch_weaken W2 W m1 m2 S2 H2).
Qed.

(* ==========================================================================
   3. The walk
   ========================================================================== *)

Theorem fprintf_proof : vfprintf_contract -> fprintf_contract.
Proof.
  intros HV. unfold fprintf_contract. intros f k fl om wend wpos wbase pos len pb fmt ps args T.
  apply leaf_fp_intro.
  - intros r1 r2 m E H. unfold getr_same in E. cbv beta in *.
    unfold arg, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m _. reflexivity.
  - apply pf_post_ext.
  - unfold leaf_fp_walk, FPRINTF, FPRINTF_K.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta.
    intros (HA0 & HMK & HDY & HPB & HK & HFMT & HR1 & HR2 & HPS & HTX & HPA & HFIT & HBLK & HIMG & HGW)
      MI TM ST LO SP FRM ITOP GG GQ.
    rewrite mkR_a0 in HA0. rewrite mkR_a1 in HFMT, HR1, HR2. rewrite mkR_sp in HBLK, HIMG.
    subst f.
    assert (HPA' : pf_args_ok m (bv_unsigned sp) (bv_unsigned sp - FPRINTF_K) (bv_unsigned a0) MemFile.MF_BLOCK
                     [a2; a3; a4; a5; a6; a7] args) by exact HPA.
    clear HPA.
    pose proof (memfile_k_place _ _ _ HMK) as HPL.
    pose proof (memfile_k_at _ _ _ HMK) as (Hf0 & Hf1 & _).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (TSK : forall x, bv_unsigned sp + -80 <= x < bv_unsigned sp ->
                    find_segment rsegs x 1 <> None \/ x < TASK_SIZE)
      by (intros x Hx; eapply stk_task; [exact TM | exact ST | lia]).
    (* what vfprintf's Pre needs from the entry memory, out of the walk tactics' reach *)
    apply fp_hide in HMK. apply fp_hide in HDY. apply fp_hide in HPB. apply fp_hide in HFMT.
    apply fp_hide in HPA'. apply fp_hide in HGW.
    (* the stack protector's two words, for the loads *)
    unfold A_GOT_GUARD, A_GUARD, wz in GG. apply fp_ro_c8 in GG.
    destruct GQ as [g GQ]. unfold A_GUARD in GQ. apply fp_ro_c8 in GQ.
    unfold A_IMG_TOP in ITOP. unfold IMG_TOP in HIMG.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 80%nat ST.
    (* +0x00 .. +0x3c: the frame, the guard, the six slots, the va_list; +0x40 jal vfprintf *)
    step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    step.
    assert (U80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80)
      by (apply unsigned_lit; lia).
    unfold fp_hold in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (MSL : va_slots mc (bv_unsigned sp - 48) [a2; a3; a4; a5; a6; a7])
        by (eapply fr_slots; [exact FR | lia]);
      assert (TMc : task_mem rsegs mc)
        by (eapply task_mem_munch; [exact TM | exact MU | exact TSK]);
      assert (GWc : guard_words mc)
        by (eapply guard_move; [exact HGW | exact MU | unfold GUARD; lia])
    end.
    eapply (leaf_fp_call _ _ _ _ _
              (HV (bv_unsigned a0) k fl om wend wpos wbase pos len pb fmt ps args T [a2; a3; a4; a5; a6; a7])
              (pf_post_ext (bv_unsigned a0) k pb T fl om wend pos len)) with (lo := lo).
    + apply leaf_fp_q_ext. intros q1 q2 m' E [H1 H2]. split; [|exact H2].
      unfold res in *. rewrite <- E. exact H1.
    + eapply (vf_pre_intro _ m _ (bv_unsigned sp));
        first [ eassumption | reflexivity | exact HFMT | exact HR1 | exact HR2
              | (rewrite mkR_a2, unsigned_lit by lia; lia) | (rewrite mkR_sp, U80; lia)
              | (unfold FPRINTF_K, IMG_TOP; lia) | lia ].
    + assumption.
    + exact TMc.
    + rewrite U80. exact ST.
    + rewrite U80. unfold VFPRINTF_K. lia.
    + rewrite U80. lia.
    + exact FRM.
    + unfold A_IMG_TOP. exact ITOP.
    + exact (proj1 GWc).
    + exact (proj2 GWc).
    + intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m2
        FRM2 FK MU2 WM2 MI2 TM2 ST2 PO.
      cbv beta in MU2, PO. unfold VFPRINTF_K in MU2. rewrite U80 in MU2, ST2.
      destruct PO as [HR HPF].
      unfold mf_place_ok, IMG_LO, IMG_TOP in HPL.
      eapply rw_cells_transport in FR; [ | exact MU2 | exact WM2 |
        unfold mf_block; cbn [disjoint_from cells_size csize Nat.add]; nat_lits;
        unfold MemFile.MF_BLOCK in *; repeat split; lia ].
      eapply ro_cells_transport in GQ; [ | exact MU2 |
        unfold mf_block; cbn [disjoint_from cells_size csize Nat.add]; nat_lits;
        unfold MemFile.MF_BLOCK in *; repeat split; lia ].
      replace (ret_pc (Z_to_bv 64 0x19740)) with (Z_to_bv 64 0x19740)
        by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      (* +0x44 .. +0x4c: the guard is unchanged *)
      step. step. step. if_false.
      (* +0x50 .. +0x5c: the epilogue *)
      step. step. step.
      release_frame FR ST2 (bv_unsigned sp).
      step.
      apply evt_done. cbv beta.
      do 4 eexists. split; [reflexivity|].
      split; [exact FRM2|]. split; [exact FK|].
      split; [apply regs_preserved_mkR|].
      split.
      { eapply munch_join; [exact MU | exact MU2 | |];
          unfold sub_fp, mf_block; cbn [outside]; intros; unfold MemFile.MF_BLOCK in *; lia. }
      split; [exact (wmono_trans rsegs _ _ _ WM WM2)|].
      split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|].
      split; [|exact HPF].
      exact HR.
Qed.

(* fprintf closed: vfprintf's contract is lib/Prog/vfprintf.v `vfprintf_proof` (no premise). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require vfprintf.

Theorem fprintf_proof_closed : fprintf_contract.
Proof. exact (fprintf_proof vfprintf.vfprintf_proof). Qed.
