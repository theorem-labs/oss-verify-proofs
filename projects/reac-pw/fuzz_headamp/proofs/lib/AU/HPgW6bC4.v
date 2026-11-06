(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC4.v at f3898085bda (with c2_envz /
   c2_all256 / c2_regv from RPgW6aC2h.v and tl_val_at from RPgW6aTail.v) for reac-pw/fuzz_headamp's image B: image
   B's case-4 code (the pointer-overflow test before the input read, the input byte's shadow check with its slow block
   0x827ec, the join through 0x82610 / 0x82614), image B's entry state HPgW6bBase.hb_entry with a6 pinned to 1, the
   post HPgSteps.hdu_blk_postE with HPgCaseBJ.cj_J_R and cj_wr, e62's bytes through HPgCaseBJ.cj_e62_tyszv. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the block lemma hw6b_c4 of
   lib/AU/HPgW6bBase.v, case 4 of ent_build's `switch (kind % 10)` (pod.h:326-331) inside LLVMFuzzerTestOneInput
   (0x80c40), from the case entry 0x81c68 to the join J 0x82618. Proves no function (kind: segment lemma).

   THE CODE (registers as in HPgW6bBase.v: s1 = R, s11 = SHADOW_OFF, s2 = c the cursor, s4 = |r| what is left,
   a7 = c - 1, t1 = |r| + 1, a6 = 1):
     0x81c68  beqz s4 -> 0x82078                   no byte is left: v = 0 and nothing is read
     0x81c6c  addi a0,s2,1; ld s7,0x148(s1) (= pp); bltu a6,a0 -> 0x81c7c, else j 0x83a14 (the pointer-overflow
              trap, never taken: 1 < c + 1)
     0x81c7c  srli a0,s2,3; add a0,a0,s11; lb a0,0(a0); ld s4,0x130(s1) (= &e62); bnez a0 -> 0x827ec
              (the input byte's shadow check; slow block 0x827ec `andi a1,s2,7; blt a1,a0 -> 0x81c90; j errpath`)
     0x81c90  lbu a0,0(s2) (= v); t1 := t1 - 2; s2 := a7 + 2
     0x81c9c .. 0x81cb4  a0 := (v - ((v * 0xab) >> 9) - 2 * ((v * 0xab) >> 9)) & 0xff, which is v mod 3 for every
              one of the 256 bytes (pod.h:327); j 0x82088
     0x82078  ld s7,0x148(s1); t1 := 0; a0 := 0; ld s4,0x130(s1)
     0x82088  sw 2,0(s4) (e62.type = POD_BOOL); sw 4,4(s4) (e62.size = 4); sw a0,8(s4) (e62.body[0..4) = v mod 3);
              j 0x82610
     0x82610  mv a3,s2; ld s2,0x138(s1) (= pp + 0x4000)                                        -> J 0x82618
   The real-frame cells read: R+0x130 (&e62 = F+0x210), R+0x138 (pp+0x4000), R+0x148 (pp); none is written. The three
   stores into e62 ask no obligation: e62 is in scope at the case entry (its 13 shadow granules are 0) and the shadow
   entry hb_SH covers it. The one obligation the run leaves is the input read's, paid from hw6b_inp's
   range_addressable over the input bytes.
   THE PROOF: the entry state hb_entry with a6 (x16) pinned to the literal 1 (HPgSteps.st_ok_pin_lit), so that the
   engine decides the pointer-overflow branch from the cursor's interval; the branch on s4 split by srr_branch_tok;
   one engine run per arm to J (the token engine follows the shadow check's slow block itself); the post read off the
   run's final state: the registers from their symbolic values, e62's 104 bytes from the three stored chunks and the
   92 bytes of the zero chunk that is left, every byte outside cj_wr R F hw6b_ws from the run's frame. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSteps HPgCaseBJ HPgW6bBase HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================== the model ======================================== *)
(* ent_build of a turn whose kind byte is 4 mod 10 (pod.h:326-331) *)
Lemma hc4_model : forall (bb : byte) (l : list byte), bv_unsigned bb mod 10 = 4 ->
  ent_build (bb :: l) = (Ent POD_BOOL 4 (le32 (fst (fuzz_u8 l) mod 3)), snd (fuzz_u8 l)).
Proof.
intros bb l H. unfold ent_build. cbn [fuzz_u8]. rewrite H. cbn [Z.to_nat].
destruct (fuzz_u8 l) as [v l1] eqn:E. cbn [fst snd]. reflexivity.
Qed.

(* ======================================== the arithmetic ======================================== *)
(* a0 at 0x81cb8 as the engine computes it from the input byte (atom 35): the mul-shift remainder of pod.h:327,
   checked for all 256 bytes *)
Definition hc4_a0 : sv :=
SAlu ALU_AND
  (SAlu ALU_SUB
     (SAlu ALU_SUB (SExt false 8 (SOff 35 0))
        (SAlu ALU_SRL (SMd M_MUL (SExt false 8 (SOff 35 0)) (SLit 171)) (SLit 9)))
     (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SExt false 8 (SOff 35 0)) (SLit 171)) (SLit 9)) (SLit 1)))
  (SLit 255).
Lemma hc4_a0_val : forall E m, ew E 35 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E hc4_a0 = Z_to_bv 64 (m mod 3).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (cb_envz m) hc4_a0); [unfold hc4_a0; cbn [sv_denot ew cb_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (cb_all256 (fun m => bv_unsigned (sv_denot (cb_envz m) hc4_a0) =? bv_unsigned (Z_to_bv 64 (m mod 3)))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.

(* ======================================== the entry state ======================================== *)
(* the entry state of HPgW6bBase.v with a6 pinned to the literal 1 *)
Definition hc4_pin (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (sr_set (ss_regs ss) (16%bv : bv 5) (SLit 1)) (ss_mem ss) (ss_resv ss) (ss_facts ss).

(* the bytes a case may write: the cells R+0x58 and R+0x110 and e62 *)
Lemma hc4_wr : forall R F a,
  (R + 0x58 <= a < R + 0x60 \/ R + 0x110 <= a < R + 0x118 \/ F + 0x210 <= a < F + 0x278) ->
  cj_wr R F hw6b_ws a.
Proof.
intros R F a H. unfold cj_wr, hw6b_ws, HSU_E62. destruct H as [H|[H|H]].
- right. left. apply Exists_cons_hd. lia.
- right. left. apply Exists_cons_tl. apply Exists_cons_hd. lia.
- right. right. lia.
Qed.

(* a chunk of a region of a final state, by its place in the chunk list *)
Ltac hc4_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).
(* a register of the state after a run, as its symbolic value's denotation *)
Ltac hc4_regv HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity);
    cbn [sv_denot]; rewrite ?ew_ewset_other by lia
  end.
(* a value below 2^32, the bound of a 4-byte chunk *)
Ltac hc4_rng := change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia.
Lemma hc4_mod3_rng : forall m, 0 <= m mod 3 < 2 ^ (8 * Z.of_N 4).
Proof.
intros m. pose proof (Z.mod_pos_bound m 3 ltac:(lia)) as H. change (2 ^ (8 * Z.of_N 4)) with 4294967296.
set (x := m mod 3) in *. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================================== reading the final state ======================================== *)
(* a byte of a zero chunk of region i of a final state *)
Lemma hc4_zero_at : forall E ss (H : word -> bool) ms i rg off len a j,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some rg ->
  In (YP09.mkChunk off (CZero len)) (YP09.r_chunks rg) ->
  a = base_val E (YP09.r_base rg) + off -> 0 <= j < len ->
  aview rsegs H (ms_mem ms) (a + j) = Some 0.
Proof.
intros E ss H ms i rg off len a j HS Hi Hc -> Hj. unfold aview.
rewrite (hb_chunk_zero E (mrestrict H (ms_mem ms)) rg off len
  (hb_region E ss (restrict H ms) rg HS (nth_error_In _ _ Hi)) Hc j Hj).
reflexivity.
Qed.
(* every byte outside the run's write windows is kept *)
Lemma hc4_keep : forall (W : world rsegs) E (rs : smem) (m0 m1 : word -> option byte) (Wr : Z -> Prop),
  frame_of E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
  (forall rg, In rg rs -> forall a, base_val E (YP09.r_base rg) + YP09.r_wlo rg <= a <
     base_val E (YP09.r_base rg) + YP09.r_whi rg -> Wr a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) m1 a = aview rsegs (w_H W) m0 a.
Proof.
intros W E rs m0 m1 Wr HFr Hwr a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
intros (rg & Hin & Hr). rewrite unsigned_lit_small in Hr by lia. exact (Hn (Hwr rg Hin a Hr)).
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ======================================== the block lemma ======================================== *)
Theorem hw6b_c4 : hw6b_c4_stmt B MT.
Proof using MTL.
unfold hw6b_c4_stmt, hw6b_case_stmt. cbv beta.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b r Hctx Hkd Hin _.
destruct Hctx as (HJ & HR32 & HRsp & HspR & Hown & HF & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & H13 & V40 & Ve8 & V118 & V130 & V138 & V148
  & Hkdr & Hpp1 & Hpp2 & HF1 & HF2 & HF32 & HRc & HFpres & Hez & Hera & Hehull & Hc1 & Hinp & Hinhull & Hdis).
destruct Hinp as (Hg & Hrain & Hc0 & Hcle & Ham & Hdisw).
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@asan_consts rc) as (Hac & _).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
rewrite HTS in HspR, HRc, Hdisw.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & Happ).
rewrite <- HF in Happ. change (fs_frame_bytes 4) with 1024 in Happ.
(* the closed bounds the entry state asks for *)
assert (HpcD4 : 0 <= HB_D4) by (unfold HB_D4; lia).
assert (HRa : alloc_ceiling <= R) by (clear - HRc; lia).
assert (HRb : R + 0x220 <= 2 ^ 47) by (clear - HRsp Hshi H47; lia).
assert (HR16 : R mod 16 = 0).
{ clear - HR32. pose proof (Z.div_mod R 32 ltac:(lia)) as E. rewrite HR32, Z.add_0_r in E. rewrite E.
  replace (32 * (R / 32)) with ((2 * (R / 32)) * 16) by ring. apply Z_mod_mult. }
assert (Hcb : 1 <= c <= 2 ^ 47 - 1).
{ clear - Hc1 Ham. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
clear Ham.
assert (Hpp0 : 0 <= pp) by (clear - Hpp1; lia).
assert (Hpp4 : pp + 0x4000 < 2 ^ 64) by (clear - Hpp2 Hac; unfold Layout.PP_SIZE in Hpp2; lia).
assert (Hshdw : forall a, F + 0x210 <= a < F + 0x278 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)).
{ clear - Happ. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. intros a Ha. lia. }
assert (HpR : forall o, (0x58 <= o < 0x60 \/ 0x110 <= o < 0x118) -> apresent (w_H W) memc (R + o)).
{ intros o Ho. apply Hpres. lia. }
assert (HpE : forall o, 0 <= o < 104 -> apresent (w_H W) memc (F + 0x210 + o)).
{ intros o Ho. replace (F + 0x210 + o) with (F + (0x210 + o)) by lia. apply HFpres. lia. }
assert (HwF : forall a, F + 0x210 <= a < F + 0x278 -> in_frames lyc own a).
{ intros a Ha. exists 4, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd]. rewrite <- HF.
  change (fs_frame_bytes 4) with 1024. lia. }
set (e8 := (- (F + 0x219)) mod 2 ^ 64) in *.
destruct r as [|b0 r'].
- (* ======================= no byte is left: 0x81c68 -> 0x82078 ======================= *)
  assert (E18 : ew (Ereg regs (hb_extra F pp e8 0)) 18 = Z_to_bv 64 c)
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E20 : ew (Ereg regs (hb_extra F pp e8 0)) 20 = Z_to_bv 64 0)
    by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); rewrite H20; reflexivity).
  assert (E9 : ew (Ereg regs (hb_extra F pp e8 0)) 9 = Z_to_bv 64 R)
    by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E32 : ew (Ereg regs (hb_extra F pp e8 0)) 32 = Z_to_bv 64 F) by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (hb_extra F pp e8 0)) 33 = Z_to_bv 64 pp) by exact (ew_Ereg_extra regs _ 1).
  assert (B9 : bv_unsigned (ew (Ereg regs (hb_extra F pp e8 0)) 9) = R)
    by (rewrite E9; apply unsigned_lit_small; lia).
  assert (B32 : bv_unsigned (ew (Ereg regs (hb_extra F pp e8 0)) 32) = F)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (HS : st_ok rsegs (Ereg regs (hb_extra F pp e8 0)) (hc4_pin (ss_hb HB_D4 false))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 HB_D4) memc (seg_rom rsegs)))).
  { unfold hc4_pin. apply (st_ok_pin_lit rsegs).
    - exact (hb_entry HB_D4 false W regs memc R F c pp 0 HpcD4 H9 H27 H18 HRa HRb HR16 HF1 HF2 Hcb ltac:(lia)
        Hpp0 Hpp4 V40 Ve8 V118 V130 V138 V148 HpR Hez HpE ltac:(intros Hb; discriminate Hb)).
    - reflexivity.
    - rewrite restrict_mkst_fx. exact H16. }
  assert (SHOK : sh_ok rsegs HBx hb_SH (Ereg regs (hb_extra F pp e8 0)) (mrestrict (w_H W) memc))
    by exact (hb_shok regs (w_H W) memc F pp e8 0 H27 HF1 HF2 Hera Hshdw).
  assert (HAE : env_agree 32 (Ereg regs (hb_extra F pp e8 0)) (Ereg regs (hb_extra F pp e8 0)))
    by apply env_agree_refl.
  unfold cfg_at. change (w64 HB_D4) with (Z_to_bv 64 HB_D4).
  srr_branch_tok hb_tbl_ok HS SHOK HBspan.
  + (* s4 = 0: the run to J *)
    aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_J.
    { (* the write windows: R+0x58 and R+0x110 in the journal's stack window, e62 in the frame (4, pos) *)
      lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?bl0 ?blc ?lyx ?ow =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp bl0 blc lyx ow) end.
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
        [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
        [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat F);
        [reflexivity | exact B32
        | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; apply HwF; lia |].
      apply awr_ok_nil. }
    (* the leaf at J *)
    apply SRr_ret. unfold hdu_blk_postE.
    lazymatch goal with
    | HS1 : st_ok _ _ _ (restrict (w_H _) ?m), HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ ?l1 ?s1 _ _ _ _,
      HFr1 : frame_of _ _ _ _ |- _ =>
      exists l1, s1, (ms_regs m), (ms_mem m); eexists;
      split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ m HS1 eq_refl) at 1; reflexivity|];
      split; [exact HJ1|];
      split; [eapply (regs_kept_of_st_ok rsegs _ _ m _ _ (w_H W) _ HS1);
              [env_agree_chain HAE | vm_compute; reflexivity]|];
      split; [reflexivity|];
      split; [apply Permutation_refl|];
      split; [cb_kio|];
      split; [apply mo_le_refl; exact MTL|];
      split;
      [ apply (hc4_keep W _ _ memc _ _ HFr1); intros rg Hin a Hr;
        cbv [ss_mem add_cond hc4_pin ss_hb hb_regions] in Hin; cbn [In] in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hb_rA hb_rB hb_rC hb_rD hb_rE hb_rF] in Hr;
        rewrite ?B9, ?B32 in Hr; first [exfalso; lia | apply hc4_wr; lia]
      | ]
    end.
    unfold cj_J_R. rewrite (hc4_model b (@nil byte) Hkd). cbn [fuzz_u8 fst snd length Z.of_nat].
    lazymatch goal with HS1 : st_ok _ _ _ (restrict _ ?m) |- _ => rename HS1 into HSf; set (msf := m) in * end.
    split; [hc4_regv HSf (13%bv : bv 5); rewrite E18, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split; [hc4_regv HSf (6%bv : bv 5); reflexivity|].
    split; [hc4_regv HSf (18%bv : bv 5); rewrite E33, unsigned_lit_small by lia; unfold w64, Layout.OFF_LEN;
            f_equal; lia|].
    split; [hc4_regv HSf (20%bv : bv 5); rewrite E32, unsigned_lit_small by lia; unfold w64, HSU_E62;
            f_equal; lia|].
    split; [hc4_regv HSf (23%bv : bv 5); rewrite E33, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    apply cj_e62_tyszv.
    * eapply (cb_val_at_rng _ _ (w_H W) msf 5%nat _ 528 4%N _ 2 F _);
        [exact HSf | reflexivity | hc4_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | hc4_rng
        | cbn; lia | unfold HSU_E62; lia].
    * eapply (cb_val_at_rng _ _ (w_H W) msf 5%nat _ 532 4%N _ 4 F _);
        [exact HSf | reflexivity | hc4_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | hc4_rng
        | cbn; lia | unfold HSU_E62; lia].
    * eapply (cb_val_at_rng _ _ (w_H W) msf 5%nat _ 536 4%N _ (0 mod 3) F _);
        [exact HSf | reflexivity | hc4_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | apply hc4_mod3_rng
        | cbn; lia | unfold HSU_E62; lia].
    * intros i Hi. eapply (hc4_zero_at _ _ (w_H W) msf 5%nat _ 540 92 _ i);
        [exact HSf | reflexivity | hc4_in | cbn [YP09.r_base base_val]; rewrite B32; unfold HSU_E62; lia | lia].
  + (* s4 <> 0 is impossible here *)
    exfalso.
    assert (Ht : (bv_unsigned (sv_denot (Ereg regs (hb_extra F pp e8 0)) (SOff 20 0)) =?
                  bv_unsigned (sv_denot (Ereg regs (hb_extra F pp e8 0)) (SLit 0))) = false) by exact Hc.
    cbn [sv_denot] in Ht. rewrite E20 in Ht. discriminate Ht.
- (* ======================= a byte is left ======================= *)
  assert (Hb0 : 0 <= bv_unsigned b0 < 256) by apply Cursor.byte_range.
  assert (E18 : ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 18 = Z_to_bv 64 c)
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E17 : ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 17 = Z_to_bv 64 (c - 1))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E6 : ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 6
    = Z_to_bv 64 (Z.of_nat (length (b0 :: r')) + 1))
    by (rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
  assert (E20 : ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 20 = Z_to_bv 64 (Z.of_nat (length (b0 :: r'))))
    by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E27 : ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 27 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E9 : ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 9 = Z_to_bv 64 R)
    by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E32 : ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 32 = Z_to_bv 64 F)
    by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 33 = Z_to_bv 64 pp)
    by exact (ew_Ereg_extra regs _ 1).
  assert (E35 : ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 35 = Z_to_bv 64 (bv_unsigned b0))
    by exact (ew_Ereg_extra regs _ 3).
  assert (B9 : bv_unsigned (ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 9) = R)
    by (rewrite E9; apply unsigned_lit_small; lia).
  assert (B32 : bv_unsigned (ew (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) 32) = F)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (Hl : 1 <= Z.of_nat (length (b0 :: r')) < 2 ^ 63) by (clear - Hcle Hcb; cbn [length] in *; lia).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 (bv_unsigned b0))
    by (destruct (Hg 0%nat ltac:(cbn [length hd_zbytes map]; lia)) as [Hv _]; exact Hv).
  rewrite Z.add_0_r in Hm0.
  assert (HS : st_ok rsegs (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) (hc4_pin (ss_hb HB_D4 true))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 HB_D4) memc (seg_rom rsegs)))).
  { unfold hc4_pin. apply (st_ok_pin_lit rsegs).
    - apply (hb_entry HB_D4 true W regs memc R F c pp (bv_unsigned b0) HpcD4 H9 H27 H18 HRa HRb HR16 HF1 HF2 Hcb Hb0
        Hpp0 Hpp4 V40 Ve8 V118 V130 V138 V148 HpR Hez HpE).
      intros _. split; [exact Hm0|].
      pose proof (Hdisw c ltac:(cbn [length]; lia)) as Hd1.
      pose proof (Hdis c ltac:(cbn [length]; lia)) as Hd2.
      split; lia.
    - reflexivity.
    - rewrite restrict_mkst_fx. exact H16. }
  assert (SHOK : sh_ok rsegs HBx hb_SH (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) (mrestrict (w_H W) memc))
    by exact (hb_shok regs (w_H W) memc F pp e8 (bv_unsigned b0) H27 HF1 HF2 Hera Hshdw).
  assert (HAE : env_agree 32 (Ereg regs (hb_extra F pp e8 (bv_unsigned b0)))
    (Ereg regs (hb_extra F pp e8 (bv_unsigned b0)))) by apply env_agree_refl.
  unfold cfg_at. change (w64 HB_D4) with (Z_to_bv 64 HB_D4).
  srr_branch_tok hb_tbl_ok HS SHOK HBspan.
  + (* s4 = 0 is impossible here *)
    exfalso.
    assert (Ht : (bv_unsigned (sv_denot (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) (SOff 20 0)) =?
                  bv_unsigned (sv_denot (Ereg regs (hb_extra F pp e8 (bv_unsigned b0))) (SLit 0))) = true)
      by exact Hc.
    cbn [sv_denot] in Ht. rewrite E20 in Ht.
    rewrite (unsigned_lit_small (Z.of_nat (length (b0 :: r')))) in Ht by lia.
    rewrite (unsigned_lit_small (Z.of_nat (length (b0 :: r')) + 0)) in Ht by lia.
    rewrite (unsigned_lit_small 0) in Ht by lia.
    apply Z.eqb_eq in Ht. lia.
  + (* s4 <> 0: the pointer-overflow test, the read of the input byte and the run to J *)
    aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_J.
    { (* the shadow check of the cursor: its one byte is addressable *)
      apply (obl_of_range rsegs (w_H W) memc _ HBx _ _ c (Z.of_nat (length (b0 :: r'))) Hrain).
      - apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
      - rewrite (U_atom _ 18 c E18) by lia. lia.
      - rewrite (U_atom _ 18 c E18) by lia. lia. }
    { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?bl0 ?blc ?lyx ?ow =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp bl0 blc lyx ow) end.
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
        [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
        [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat F);
        [reflexivity | exact B32
        | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; apply HwF; lia |].
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
      apply awr_ok_nil. }
    (* the leaf at J *)
    apply SRr_ret. unfold hdu_blk_postE.
    lazymatch goal with
    | HS1 : st_ok _ _ _ (restrict (w_H _) ?m), HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ ?l1 ?s1 _ _ _ _,
      HFr1 : frame_of _ _ _ _ |- _ =>
      exists l1, s1, (ms_regs m), (ms_mem m); eexists;
      split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ m HS1 eq_refl) at 1; reflexivity|];
      split; [exact HJ1|];
      split; [eapply (regs_kept_of_st_ok rsegs _ _ m _ _ (w_H W) _ HS1);
              [env_agree_chain HAE | vm_compute; reflexivity]|];
      split; [reflexivity|];
      split; [apply Permutation_refl|];
      split; [cb_kio|];
      split; [apply mo_le_refl; exact MTL|];
      split;
      [ apply (hc4_keep W _ _ memc _ _ HFr1); intros rg Hin a Hr;
        cbv [ss_mem add_cond hc4_pin ss_hb hb_regions] in Hin; cbn [In] in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hb_rA hb_rB hb_rC hb_rD hb_rE hb_rF hb_rI] in Hr;
        rewrite ?B9, ?B32 in Hr; first [exfalso; lia | apply hc4_wr; lia]
      | ]
    end.
    unfold cj_J_R. rewrite (hc4_model b (b0 :: r') Hkd). cbn [fuzz_u8 fst snd].
    lazymatch goal with HS1 : st_ok _ _ _ (restrict _ ?m) |- _ => rename HS1 into HSf; set (msf := m) in * end.
    split; [hc4_regv HSf (13%bv : bv 5); rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal;
            cbn [length]; lia|].
    split; [hc4_regv HSf (6%bv : bv 5); rewrite E6, unsigned_lit_small by lia; unfold w64; f_equal;
            cbn [length]; lia|].
    split; [hc4_regv HSf (18%bv : bv 5); rewrite E33, unsigned_lit_small by lia; unfold w64, Layout.OFF_LEN;
            f_equal; lia|].
    split; [hc4_regv HSf (20%bv : bv 5); rewrite E32, unsigned_lit_small by lia; unfold w64, HSU_E62;
            f_equal; lia|].
    split; [hc4_regv HSf (23%bv : bv 5); rewrite E33, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    apply cj_e62_tyszv.
    * eapply (cb_val_at_rng _ _ (w_H W) msf 5%nat _ 528 4%N _ 2 F _);
        [exact HSf | reflexivity | hc4_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B32
        | reflexivity | hc4_rng | cbn; lia | unfold HSU_E62; lia].
    * eapply (cb_val_at_rng _ _ (w_H W) msf 5%nat _ 532 4%N _ 4 F _);
        [exact HSf | reflexivity | hc4_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B32
        | reflexivity | hc4_rng | cbn; lia | unfold HSU_E62; lia].
    * eapply (cb_val_at_rng _ _ (w_H W) msf 5%nat _ 536 4%N hc4_a0 (bv_unsigned b0 mod 3) F _);
        [exact HSf | reflexivity | hc4_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B32
        | apply hc4_a0_val; [rewrite ?ew_ewset_other by lia; exact E35 | exact Hb0]
        | apply hc4_mod3_rng | cbn; lia | unfold HSU_E62; lia].
    * intros i Hi. eapply (hc4_zero_at _ _ (w_H W) msf 5%nat _ 540 92 _ i);
        [exact HSf | reflexivity | hc4_in
        | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; rewrite B32; unfold HSU_E62; lia | lia].
Qed.

End d.
End b.

Print Assumptions hw6b_c4.
