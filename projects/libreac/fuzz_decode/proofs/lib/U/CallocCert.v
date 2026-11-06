From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require PropExec MState Mem Cells Exec Frame Step.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require memset_ro_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0 KindBGlue AllocCut CallocAZ CallocKB CallocRun.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import
  YK11 YK0s YM05 YM06 YP09 YO0i YO0f YO0g YO0d YO0s YO0u YO0x YO10 YH00 YH02 YH03 YN03 YN2b YN0a YN0d YN0e YN07
  YN0i YN10 YN23 YN33.
Import ListNotations.
Open Scope Z_scope.
Definition kr (a b : bvmap 5 word) : Prop :=
  forall r, r = 3 \/ r = 4 \/ 18 <= r <= 27 -> getr b (Z_to_bv 5 r) = getr a (Z_to_bv 5 r).
Ltac kr_tac := let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in intros r Hr;
  assert (Hc : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
               r = 26 \/ r = 27) by lia;
  repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity.
Lemma kr_eq : forall a b c, (forall r, getr b r = getr c r) -> kr a c -> kr a b.
Proof. intros a b c H K r Hr. rewrite H. exact (K r Hr). Qed.
Lemma kr_trans : forall a b c, kr a b -> kr b c -> kr a c.
Proof. intros a b c H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma kr_pres : forall a b, regs_preserved a b -> kr a b.
Proof. intros a b H r Hr. apply H. unfold callee_saved. lia. Qed.
Lemma pres_kr : forall a b, kr a b -> getr b 2 = getr a 2 -> getr b 8 = getr a 8 -> getr b 9 = getr a 9 ->
  regs_preserved a b.
Proof.
  intros a b K H2 H8 H9 r Hr. unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [exact H2 | apply K; lia | apply K; lia | exact H8 | exact H9 |].
  apply K. lia.
Qed.
Lemma pw_mid {X} : forall (R : X -> X -> Prop) l1 x l2 y, pairwise R (l1 ++ x :: l2) -> In y (l1 ++ l2) -> R y x \/ R x y.
Proof.
  intros R l1. induction l1 as [|z l1 IH]; intros x l2 y H Hy; cbn in *.
  - right. apply (proj1 H). exact Hy.
  - destruct H as [Hz Hp]. destruct Hy as [<-|Hy].
    + left. apply Hz. apply in_or_app. right. left. reflexivity.
    + exact (IH x l2 y Hp Hy).
Qed.
Lemma seg_img : forall x seg, find_segment rsegs x 1 = Some seg -> in_img src0_msyms x.
Proof.
  intros x seg H. destruct (kb_find_segment rsegs x 1 seg H) as (Hin & H1 & H2).
  assert (C : forallb (fun s => (0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x50000))
                rsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply andb_prop in C as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2. apply in_img1_img. unfold YN0d.in_img1. lia.
Qed.
Lemma noseg : forall x, ~ in_img src0_msyms x -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. exact (Hx (seg_img x seg E)).
Qed.
Lemma spZ_lit : forall regs x, getr regs 2 = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> spZ regs = x.
Proof. intros regs x H Hx. unfold spZ. rewrite H. apply MState.unsigned_lit. exact Hx. Qed.
Lemma fin_pres : forall regs regs7 regs', 32 <= spZ regs < 2 ^ 63 ->
  getr regs7 2 = Z_to_bv 64 (spZ regs - 32) -> kr regs regs7 ->
  getr regs' 2 = Z_to_bv 64 (spZ regs7 + 32) -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  kr regs7 regs' -> regs_preserved regs regs'.
Proof.
  intros regs regs7 regs' Hs R2 K7 F2 F8 F9 K'.
  apply pres_kr; [exact (kr_trans _ _ _ K7 K') | | exact F8 | exact F9].
  rewrite F2, (spZ_lit regs7 _ R2) by lia. replace (spZ regs - 32 + 32) with (spZ regs) by lia.
  unfold spZ. apply Z_to_bv_bv_unsigned.
Qed.
Lemma blk_cells : forall (mem5 : word -> option byte) Q mn, 0 <= Q -> Q + mn <= 2 ^ 64 -> 0 <= mn ->
  (forall i, 0 <= i < mn -> present mem5 (Q + i)) -> exists blk, Step.rw_cells rsegs mem5 Q [Cells.CB (Z.to_nat mn) blk].
Proof.
  intros mem5 Q mn H0 H1 Hmn HP.
  assert (ST : Frame.stk rsegs mem5 Q (Q + mn)).
  { split; [lia|]. split; [lia|]. intros a Ha. destruct (HP (a - Q) ltac:(lia)) as [b Hb].
    replace (Q + (a - Q)) with a in Hb by lia.
    unfold Mem.wa, Mem.mrd, wview. rewrite Hb. split; [discriminate | exists b; reflexivity]. }
  destruct (Frame.stk_carve rsegs mem5 Q (Q + mn) (Z.to_nat mn) ST ltac:(lia)) as [_ [blk BLK]].
  exists blk. rewrite Z2Nat.id in BLK by lia. replace (Q + mn - mn) with Q in BLK by lia. exact BLK.
Qed.
Lemma blk_not_ro : forall Q mn, 0 <= Q -> Q + mn < 2 ^ 64 ->
  (forall i, 0 <= i < mn -> ~ in_img src0_msyms (Q + i)) -> RoAdapt.not_ro rsegs Q mn.
Proof.
  intros Q mn H0 H1 HI i Hi. unfold Mem.ro_addr. rewrite Mem.wa_unsigned by lia.
  rewrite (noseg (Q + i) (HI i Hi)). reflexivity.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Abbreviation ROM := (seg_rom src0segs).
Ltac kfin := first [reflexivity | kr_tac | assumption].
Ltac ksplit := first [kfin | split; [kfin | ksplit]].
Lemma s_entry : forall regs mem md mn (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Frame.stk rsegs mem (spZ regs - 32) (spZ regs) ->
  bv_unsigned (getr regs 11) * bv_unsigned (getr regs 10) = mn -> mn < 4096 ->
  (forall regs1 mem1 junk,
     getr regs1 1 = Z_to_bv 64 0x14bcc -> getr regs1 2 = Z_to_bv 64 (spZ regs + -32) ->
     getr regs1 4 = getr regs 4 -> getr regs1 8 = getr regs 8 -> getr regs1 9 = Z_to_bv 64 mn ->
     getr regs1 10 = Z_to_bv 64 mn -> kr regs regs1 ->
     Step.rw_cells rsegs mem1 (spZ regs + -32)
       [Cells.CB 8 junk; Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)] ->
     Frame.munch [(spZ regs + -32, spZ regs)] mem mem1 -> Frame.wmono rsegs mem mem1 ->
     P (mkCfg (mkst regs1 (Z_to_bv 64 src0_A_malloc) mem1 ROM) md)) ->
  SR src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_calloc) mem ROM) md) P.
Proof using.
  intros regs mem md mn P Hh Hl ST HP HMN HK.
  apply (kb_run src0_msyms regs (Z_to_bv 64 src0_A_calloc) mem md
    (fun R pc' mem' => exists junk, pc' = Z_to_bv 64 src0_A_malloc /\
       getr R 1 = Z_to_bv 64 0x14bcc /\ getr R 2 = Z_to_bv 64 (spZ regs + -32) /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = Z_to_bv 64 mn /\ getr R 10 = Z_to_bv 64 mn /\ kr regs R /\
       Step.rw_cells rsegs mem' (spZ regs + -32)
         [Cells.CB 8 junk; Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)] /\
       Frame.munch [(spZ regs + -32, spZ regs)] mem mem' /\ Frame.wmono rsegs mem mem') P Hh Hl).
  - unfold rmk. eapply Exec.evt_mono.
    + eapply run_entry; [exact ST | unfold spZ in *; lia | exact HP | exact HMN].
    + intros ms' (a2' & m1 & junk & -> & FR & MU & WM). do 3 eexists. split; [reflexivity|].
      exists junk. ksplit.
  - intros R pc' mem' regs' (junk & -> & H1 & H2 & H4 & H8 & H9 & H10 & KR & FR & MU & WM) HR.
    apply SR_ret. apply (HK regs' mem' junk); try (rewrite HR; assumption); try assumption.
    exact (kr_eq _ _ _ HR KR).
Qed.
Lemma s_null : forall regs5 mem5 md5 junk rao s0o s1o (P : config -> Prop),
  m_halted md5 = None -> m_vm_lazy md5 = [] -> getr regs5 10 = Z_to_bv 64 0 ->
  Step.rw_cells rsegs mem5 (spZ regs5) [Cells.CB 8 junk; Cells.C8 s1o; Cells.C8 s0o; Cells.C8 rao] ->
  (forall regs', getr regs' 2 = Z_to_bv 64 (spZ regs5 + 32) -> getr regs' 8 = s0o -> getr regs' 9 = s1o ->
     getr regs' 10 = Z_to_bv 64 0 -> kr regs5 regs' -> P (mkCfg (mkst regs' (MState.ret_pc rao) mem5 ROM) md5)) ->
  SR src0segs (mkCfg (mkst regs5 (Z_to_bv 64 0x14bcc) mem5 ROM) md5) P.
Proof using.
  intros regs5 mem5 md5 junk rao s0o s1o P Hh Hl H10 FR HK.
  apply (kb_run src0_msyms regs5 (Z_to_bv 64 0x14bcc) mem5 md5
    (fun R pc' mem' => pc' = MState.ret_pc rao /\ mem' = mem5 /\ getr R 2 = Z_to_bv 64 (spZ regs5 + 32) /\
       getr R 8 = s0o /\ getr R 9 = s1o /\ getr R 10 = Z_to_bv 64 0 /\ kr regs5 R) P Hh Hl).
  - unfold rmk. rewrite H10. eapply Exec.evt_mono.
    + eapply run_null. exact FR.
    + intros ms' ->. do 3 eexists. split; [reflexivity|]. ksplit.
  - intros R pc' mem' regs' (-> & -> & H2 & H8 & H9 & H10' & KR) HR. apply SR_ret.
    apply HK; try (rewrite HR; assumption). exact (kr_eq _ _ _ HR KR).
Qed.
Lemma s_some : forall regs5 mem5 md5 rb (P : config -> Prop),
  m_halted md5 = None -> m_vm_lazy md5 = [] -> bv_eqb (getr regs5 10) (Z_to_bv 64 0) = false ->
  Step.ro_cells rsegs mem5 0x4f118 [Cells.CB 4 rb] ->
  (forall regs6, getr regs6 2 = getr regs5 2 -> getr regs6 8 = getr regs5 10 -> getr regs6 9 = getr regs5 9 ->
     kr regs5 regs6 -> SR src0segs (mkCfg (mkst regs6 (Z_to_bv 64 0x14be0) mem5 ROM) md5) P) ->
  (forall regs6, getr regs6 1 = Z_to_bv 64 0x14cac -> getr regs6 2 = getr regs5 2 -> getr regs6 8 = getr regs5 10 ->
     getr regs6 9 = getr regs5 9 -> getr regs6 10 = getr regs5 10 -> kr regs5 regs6 ->
     SR src0segs (mkCfg (mkst regs6 (Z_to_bv 64 src0_A_malloc_allzerop) mem5 ROM) md5) P) ->
  SR src0segs (mkCfg (mkst regs5 (Z_to_bv 64 0x14bcc) mem5 ROM) md5) P.
Proof using.
  intros regs5 mem5 md5 rb P Hh Hl Hnz RB HK1 HK2.
  apply (kb_run src0_msyms regs5 (Z_to_bv 64 0x14bcc) mem5 md5
    (fun R pc' mem' => mem' = mem5 /\
       ((pc' = Z_to_bv 64 0x14be0 /\ getr R 2 = getr regs5 2 /\ getr R 8 = getr regs5 10 /\ getr R 9 = getr regs5 9 /\
         kr regs5 R) \/
        (pc' = Z_to_bv 64 0x164e8 /\ getr R 1 = Z_to_bv 64 0x14cac /\ getr R 2 = getr regs5 2 /\
         getr R 8 = getr regs5 10 /\ getr R 9 = getr regs5 9 /\ getr R 10 = getr regs5 10 /\ kr regs5 R))) P Hh Hl).
  - unfold rmk. eapply Exec.evt_mono.
    + eapply run_some; [exact Hnz | exact RB].
    + intros ms' [(a0r & ->) | ->]; do 3 eexists; (split; [reflexivity|]); (split; [reflexivity|]).
      * left. ksplit.
      * right. ksplit.
  - intros R pc' mem' regs' (-> & [(-> & H2 & H8 & H9 & KR) | (-> & H1 & H2 & H8 & H9 & H10 & KR)]) HR.
    + apply HK1; try (rewrite HR; assumption). exact (kr_eq _ _ _ HR KR).
    + apply HK2; try (rewrite HR; assumption). exact (kr_eq _ _ _ HR KR).
Qed.
Lemma s_azret : forall regs7 mem5 md5 junk rao s0o s1o (P : config -> Prop),
  m_halted md5 = None -> m_vm_lazy md5 = [] ->
  Step.rw_cells rsegs mem5 (spZ regs7) [Cells.CB 8 junk; Cells.C8 s1o; Cells.C8 s0o; Cells.C8 rao] ->
  (bv_eqb (getr regs7 10) (Z_to_bv 64 0) = false -> forall regs', getr regs' 2 = Z_to_bv 64 (spZ regs7 + 32) ->
     getr regs' 8 = s0o -> getr regs' 9 = s1o -> getr regs' 10 = getr regs7 8 -> kr regs7 regs' ->
     P (mkCfg (mkst regs' (MState.ret_pc rao) mem5 ROM) md5)) ->
  (forall regs', getr regs' 2 = getr regs7 2 -> getr regs' 8 = getr regs7 8 -> getr regs' 9 = getr regs7 9 ->
     kr regs7 regs' -> SR src0segs (mkCfg (mkst regs' (Z_to_bv 64 0x14be0) mem5 ROM) md5) P) ->
  SR src0segs (mkCfg (mkst regs7 (Z_to_bv 64 0x14cac) mem5 ROM) md5) P.
Proof using.
  intros regs7 mem5 md5 junk rao s0o s1o P Hh Hl FR HK1 HK2.
  apply (kb_run src0_msyms regs7 (Z_to_bv 64 0x14cac) mem5 md5
    (fun R pc' mem' => mem' = mem5 /\
       ((bv_eqb (getr regs7 10) (Z_to_bv 64 0) = false /\ pc' = MState.ret_pc rao /\
         getr R 2 = Z_to_bv 64 (spZ regs7 + 32) /\ getr R 8 = s0o /\ getr R 9 = s1o /\ getr R 10 = getr regs7 8 /\
         kr regs7 R) \/
        (pc' = Z_to_bv 64 0x14be0 /\ getr R 2 = getr regs7 2 /\ getr R 8 = getr regs7 8 /\ getr R 9 = getr regs7 9 /\
         kr regs7 R))) P Hh Hl).
  - unfold rmk. eapply Exec.evt_mono.
    + eapply run_azret. exact FR.
    + intros ms' [(Hz & ->) | ->]; do 3 eexists; (split; [reflexivity|]); (split; [reflexivity|]).
      * left. split; [exact Hz|]. ksplit.
      * right. ksplit.
  - intros R pc' mem' regs' (-> & [(Hz & -> & H2 & H8 & H9 & H10 & KR) | (-> & H2 & H8 & H9 & KR)]) HR.
    + apply SR_ret. apply HK1; try (rewrite HR; assumption); try assumption. exact (kr_eq _ _ _ HR KR).
    + apply HK2; try (rewrite HR; assumption). exact (kr_eq _ _ _ HR KR).
Qed.
Lemma s_clear : forall regs6 mem5 md5 junk rao s0o s1o mn blk (P : config -> Prop),
  m_halted md5 = None -> m_vm_lazy md5 = [] ->
  Step.rw_cells rsegs mem5 (spZ regs6) [Cells.CB 8 junk; Cells.C8 s1o; Cells.C8 s0o; Cells.C8 rao] ->
  getr regs6 9 = Z_to_bv 64 mn -> 0 <= mn < 4096 ->
  Step.rw_cells rsegs mem5 (bv_unsigned (getr regs6 8)) [Cells.CB (Z.to_nat mn) blk] ->
  RoAdapt.not_ro rsegs (bv_unsigned (getr regs6 8)) mn -> MemNorm.ro_agree rsegs mem5 ->
  (forall regs' mem', getr regs' 2 = Z_to_bv 64 (spZ regs6 + 32) -> getr regs' 8 = s0o -> getr regs' 9 = s1o ->
     getr regs' 10 = getr regs6 8 -> kr regs6 regs' ->
     Frame.munch [(bv_unsigned (getr regs6 8), bv_unsigned (getr regs6 8) + mn)] mem5 mem' ->
     Frame.wmono rsegs mem5 mem' ->
     Step.rw_cells rsegs mem' (bv_unsigned (getr regs6 8)) [Cells.CB (Z.to_nat mn) (repeat (Z_to_bv 8 0) (Z.to_nat mn))] ->
     P (mkCfg (mkst regs' (MState.ret_pc rao) mem' ROM) md5)) ->
  SR src0segs (mkCfg (mkst regs6 (Z_to_bv 64 0x14be0) mem5 ROM) md5) P.
Proof using.
  intros regs6 mem5 md5 junk rao s0o s1o mn blk P Hh Hl FR H9 Hmn BLK NRO RO HK.
  apply (kb_run src0_msyms regs6 (Z_to_bv 64 0x14be0) mem5 md5
    (fun R pc' mem' => pc' = MState.ret_pc rao /\ getr R 2 = Z_to_bv 64 (spZ regs6 + 32) /\ getr R 8 = s0o /\
       getr R 9 = s1o /\ getr R 10 = getr regs6 8 /\ kr regs6 R /\
       Frame.munch [(bv_unsigned (getr regs6 8), bv_unsigned (getr regs6 8) + mn)] mem5 mem' /\
       Frame.wmono rsegs mem5 mem' /\
       Step.rw_cells rsegs mem' (bv_unsigned (getr regs6 8))
         [Cells.CB (Z.to_nat mn) (repeat (Z_to_bv 8 0) (Z.to_nat mn))]) P Hh Hl).
  - unfold rmk. rewrite H9. eapply Exec.evt_mono.
    + eapply run_clear; [exact FR | exact Hmn | exact BLK | exact NRO | exact RO].
    + intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & _ & Z).
      rewrite MState.unsigned_lit in MU, Z by lia.
      replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in Z by reflexivity.
      do 3 eexists. split; [reflexivity|].
      ksplit.
  - intros R pc' mem' regs' (-> & H2 & H8 & H9' & H10 & KR & MU & WM & Z) HR. apply SR_ret.
    apply HK; try (rewrite HR; assumption); try assumption. exact (kr_eq _ _ _ HR KR).
Qed.
Record ctx5 (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (mn : Z)
  (L5 : layout) (A5 : astate) (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) (junk : list byte) :
  Prop := {
  c_mn : 0 <= mn < 4096;
  c_ra : YK0s.ret_ok (getr regs 1);
  c_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + CALLOC_STACK <= spZ regs /\ spZ regs < 2 ^ 63;
  c_mid : kb_mid B0 API0 CALLOC_STACK (spZ regs) L A mem md (fun _ => False) L5 A5 mem5 md5;
  c_M5 : MRx src0_msyms L5 A5 mem5 md5;
  c_stk : forall x, spZ regs - 32 - ALLOC_STACK <= x < spZ regs - 32 -> writable_at src0segs mem5 x;
  c_fr : Step.rw_cells rsegs mem5 (spZ regs - 32)
           [Cells.CB 8 junk; Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)];
  c_r2 : getr regs5 2 = Z_to_bv 64 (spZ regs - 32);
  c_r8 : getr regs5 8 = getr regs 8;
  c_r9 : getr regs5 9 = Z_to_bv 64 mn;
  c_kr : kr regs regs5;
  c_ro : MemNorm.ro_agree rsegs mem5 }.
Lemma blk_facts : forall L5 A5 mem5 md5 q mn, MRx src0_msyms L5 A5 mem5 md5 -> In (q, mn) (user_blocks A5) ->
  4096 <= ptr_addr L5 q /\ ptr_addr L5 q + mn <= alloc_ceiling /\
  (forall i, 0 <= i < mn -> present mem5 (ptr_addr L5 q + i) /\ ~ owned src0_msyms L5 A5 (ptr_addr L5 q + i) /\
     ~ in_img src0_msyms (ptr_addr L5 q + i)).
Proof using.
  intros L5 A5 mem5 md5 q mn HM Hin.
  destruct (mr_blocks_range _ _ (MRx_laws src0_msyms) _ _ _ _ _ _ HM Hin) as [H1 H2].
  split; [exact H1|]. split; [exact H2|]. intros i Hi.
  destruct (mr_blocks _ _ (MRx_laws src0_msyms) _ _ _ _ _ _ i HM Hin Hi) as (Hp & _ & _ & Hno).
  split; [exact Hp|]. split; [exact Hno|].
  exact (MRc_blocks_img src0_msyms L5 A5 mem5 md5 q mn i (MRx_MRc _ _ _ _ _ HM) Hin Hi).
Qed.
Lemma tail_memset : forall L A regs mem md mn L5 A5 regs5 mem5 md5 junk q regs6,
  ctx5 L A regs mem md mn L5 A5 regs5 mem5 md5 junk ->
  In (q, mn) (user_blocks A5) -> ptr_addr L5 q <> 0 ->
  (exists l1 l2, user_blocks A5 = l1 ++ (q, mn) :: l2 /\ user_blocks A = l1 ++ l2) ->
  getr regs6 2 = Z_to_bv 64 (spZ regs - 32) -> getr regs6 8 = Z_to_bv 64 (ptr_addr L5 q) ->
  getr regs6 9 = Z_to_bv 64 mn -> kr regs regs6 ->
  SR src0segs (mkCfg (mkst regs6 (Z_to_bv 64 0x14be0) mem5 ROM) md5)
    (calloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md mn (Some q, A5)).
Proof using.
  intros L A regs mem md mn L5 A5 regs5 mem5 md5 junk q regs6 C Hin HQ0 HUB R2 R8 R9 K6.
  destruct C as [Cmn Cra Csp Cmid CM5 Cstk Cfr Cr2 Cr8 Cr9 Ckr Cro].
  pose proof alloc_ceiling_value as AC. destruct Csp as (Hal & Hlo & Hhi).
  destruct (blk_facts L5 A5 mem5 md5 q mn CM5 Hin) as (HQ1 & HQ2 & HB).
  destruct (mr_model _ _ (MRx_laws src0_msyms) _ _ _ _ CM5) as (Hh & Hl & _).
  pose proof Cmid as (_ & _ & _ & _ & Hst & _).
  assert (EQ : bv_unsigned (getr regs6 8) = ptr_addr L5 q) by (rewrite R8; apply MState.unsigned_lit; lia).
  assert (ES : spZ regs6 = spZ regs - 32) by (apply spZ_lit; [exact R2 | unfold CALLOC_STACK, ALLOC_STACK in *; lia]).
  destruct (blk_cells mem5 (ptr_addr L5 q) mn ltac:(lia) ltac:(lia) ltac:(lia) (fun i Hi => proj1 (HB i Hi)))
    as [blk BLK].
  apply (s_clear regs6 mem5 md5 junk (getr regs 1) (getr regs 8) (getr regs 9) mn blk _ Hh Hl).
  - rewrite ES. exact Cfr.
  - exact R9.
  - exact Cmn.
  - rewrite EQ. exact BLK.
  - rewrite EQ. apply blk_not_ro; [lia | lia | intros i Hi; exact (proj2 (proj2 (HB i Hi)))].
  - exact Cro.
  - intros regs' mem' F2 F8 F9 F10 K' MU WM ZC.
    rewrite EQ in MU, ZC. rewrite (kb_ret_pc _ Cra).
    exists L5, regs', mem', md5. split; [reflexivity|]. split.
    + refine (kb_post B0 API0 CALLOC_STACK L A regs mem md (fun _ => False) L5 A5 regs' mem' md5 _ _).
      * apply (kb_mid_noE CALLOC_STACK (spZ regs) L A mem md (fun a => False \/ (ptr_addr L5 q <= a < ptr_addr L5 q + mn))).
        -- refine (kb_mid_tail B0 API0 img_low0 CALLOC_STACK (spZ regs) L A mem md (fun _ => False) L5 A5 mem5 md5 mem'
             [(ptr_addr L5 q, ptr_addr L5 q + mn)] (fun a => ptr_addr L5 q <= a < ptr_addr L5 q + mn) Cmid MU WM _ _ _ _).
           ++ intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
              destruct (Z_le_dec (ptr_addr L5 q) (bv_unsigned x)) as [Hq1|Hq1];
                [destruct (Z_lt_le_dec (bv_unsigned x) (ptr_addr L5 q + mn)) as [Hq2|Hq2]|].
              ** intros Hn. destruct ZC as [[_ (_ & _ & Hb)] _].
                 cbn [Cells.cells_bytes Cells.cbytes] in Hb. rewrite app_nil_r, repeat_length in Hb.
                 specialize (Hb (Z.to_nat (bv_unsigned x - ptr_addr L5 q)) ltac:(lia)).
                 rewrite Z2Nat.id in Hb by lia.
                 replace (ptr_addr L5 q + (bv_unsigned x - ptr_addr L5 q)) with (bv_unsigned x) in Hb by lia.
                 unfold Mem.wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb. unfold Mem.mrd in Hb. rewrite Hn in Hb.
                 unfold PropExec.seg_rom, memory_read in Hb.
                 destruct (HB (bv_unsigned x - ptr_addr L5 q) ltac:(lia)) as (_ & _ & HNi).
                 replace (ptr_addr L5 q + (bv_unsigned x - ptr_addr L5 q)) with (bv_unsigned x) in HNi by lia.
                 pose proof (noseg (bv_unsigned x) HNi) as NS. try change (Z.of_N 1) with 1 in Hb.
                 rewrite NS in Hb. rewrite nth_error_repeat in Hb by lia. discriminate Hb.
              ** rewrite (MU x); [exact Hx | cbn [Frame.outside]; split; [lia | exact I]].
              ** rewrite (MU x); [exact Hx | cbn [Frame.outside]; split; [lia | exact I]].
           ++ intros x Hx Hs He. cbn [Frame.outside]. split; [exact He | exact I].
           ++ intros x Hx Ho. cbn [Frame.outside]. split; [|exact I]. intros Hxin.
              destruct (HB (x - ptr_addr L5 q) ltac:(lia)) as (_ & HNo & _).
              replace (ptr_addr L5 q + (x - ptr_addr L5 q)) with x in HNo by lia. exact (HNo Ho).
           ++ intros p n' i Hp Hp5 Hi. cbn [Frame.outside]. split; [|exact I].
              destruct HUB as (l1 & l2 & E5 & E).
              pose proof (mr_blocks_disjoint _ _ (MRx_laws src0_msyms) _ _ _ _ CM5) as PW.
              unfold blocks in PW. rewrite E5, map_app in PW. cbn [map] in PW.
              assert (Hy : In (ptr_addr L5 p, n') (map (fun b : sptr * Z => (ptr_addr L5 (fst b), snd b)) l1 ++
                                                  map (fun b : sptr * Z => (ptr_addr L5 (fst b), snd b)) l2)).
              { rewrite <- map_app. rewrite <- E.
                exact (in_map (fun b : sptr * Z => (ptr_addr L5 (fst b), snd b)) _ (p, n') Hp). }
              pose proof (pw_mid _ _ _ _ _ PW Hy) as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
              rewrite (Hst p n' Hp Hp5) in D. lia.
        -- intros a [[]|Ha]. destruct (HB (a - ptr_addr L5 q) ltac:(lia)) as (_ & _ & HNi).
           replace (ptr_addr L5 q + (a - ptr_addr L5 q)) with a in HNi by lia. split; [lia | exact HNi].
      * apply (fin_pres regs regs6 regs'); try assumption. unfold CALLOC_STACK, ALLOC_STACK in *. lia.
    + cbn [fst snd]. split; [rewrite F10, R8; reflexivity|]. split; [exact HQ0|]. split; [exact HUB|].
      intros i Hi. destruct ZC as [[_ (_ & _ & Hb)] _].
      cbn [Cells.cells_bytes Cells.cbytes] in Hb. rewrite app_nil_r, repeat_length in Hb.
      specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
      rewrite nth_error_repeat in Hb by lia. exact Hb.
Qed.
Lemma leaf_null : forall L A regs mem md mn L5 A5 regs5 mem5 md5 junk,
  ctx5 L A regs mem md mn L5 A5 regs5 mem5 md5 junk ->
  getr regs5 10 = Z_to_bv 64 0 -> user_blocks A5 = user_blocks A ->
  SR src0segs (mkCfg (mkst regs5 (Z_to_bv 64 0x14bcc) mem5 ROM) md5)
    (calloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md mn (None, A5)).
Proof using.
  intros L A regs mem md mn L5 A5 regs5 mem5 md5 junk C H10 UB.
  pose proof C as [Cmn Cra Csp Cmid CM5 Cstk Cfr Cr2 Cr8 Cr9 Ckr Cro].
  pose proof alloc_ceiling_value as AC. destruct Csp as (Hal & Hlo & Hhi).
  destruct (mr_model _ _ (MRx_laws src0_msyms) _ _ _ _ CM5) as (Hh & Hl & _).
  assert (ES : spZ regs5 = spZ regs - 32) by (apply spZ_lit; [exact Cr2 | unfold CALLOC_STACK, ALLOC_STACK in *; lia]).
  apply (s_null regs5 mem5 md5 junk (getr regs 1) (getr regs 8) (getr regs 9) _ Hh Hl H10); [rewrite ES; exact Cfr|].
  intros regs' F2 F8 F9 F10 K'. rewrite (kb_ret_pc _ Cra).
  exists L5, regs', mem5, md5. split; [reflexivity|]. split.
  - refine (kb_post B0 API0 CALLOC_STACK L A regs mem md (fun _ => False) L5 A5 regs' mem5 md5 Cmid _).
    apply (fin_pres regs regs5 regs'); try assumption. unfold CALLOC_STACK, ALLOC_STACK in *. lia.
  - cbn [fst snd]. split; [exact F10 | exact UB].
Qed.
Lemma leaf_some : forall L A regs mem md mn L5 A5 regs5 mem5 md5 junk q,
  ctx5 L A regs mem md mn L5 A5 regs5 mem5 md5 junk ->
  getr regs5 10 = Z_to_bv 64 (ptr_addr L5 q) -> ptr_addr L5 q <> 0 ->
  (exists l1 l2, user_blocks A5 = l1 ++ (q, mn) :: l2 /\ user_blocks A = l1 ++ l2) ->
  (allzero_block A5 q = true -> forall i, 0 <= i < mn -> mbyte src0segs mem5 (ptr_addr L5 q + i) = Some (Z_to_bv 8 0)) ->
  SR src0segs (mkCfg (mkst regs5 (Z_to_bv 64 0x14bcc) mem5 ROM) md5)
    (calloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md mn (Some q, A5)).
Proof using.
  intros L A regs mem md mn L5 A5 regs5 mem5 md5 junk q C H10 HQ0 HUB AZ.
  pose proof C as [Cmn Cra Csp Cmid CM5 Cstk Cfr Cr2 Cr8 Cr9 Ckr Cro].
  pose proof alloc_ceiling_value as AC. destruct Csp as (Hal & Hlo & Hhi).
  destruct (mr_model _ _ (MRx_laws src0_msyms) _ _ _ _ CM5) as (Hh & Hl & _).
  assert (Hin : In (q, mn) (user_blocks A5)).
  { destruct HUB as (l1 & l2 & E5 & _). rewrite E5. apply in_or_app. right. left. reflexivity. }
  destruct (blk_facts L5 A5 mem5 md5 q mn CM5 Hin) as (HQ1 & HQ2 & HB).
  assert (Hnz : bv_eqb (getr regs5 10) (Z_to_bv 64 0) = false).
  { rewrite H10. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. exact HQ0. }
  assert (ES : spZ regs5 = spZ regs - 32) by (apply spZ_lit; [exact Cr2 | unfold CALLOC_STACK, ALLOC_STACK in *; lia]).
  destruct (replaced_cells mem5) as [rb RB].
  apply (s_some regs5 mem5 md5 rb _ Hh Hl Hnz RB).
  - intros regs6 R62 R68 R69 K6.
    apply (tail_memset L A regs mem md mn L5 A5 regs5 mem5 md5 junk q regs6 C Hin HQ0 HUB).
    + rewrite R62. exact Cr2.
    + rewrite R68. exact H10.
    + rewrite R69. exact Cr9.
    + exact (kr_trans _ _ _ Ckr K6).
  - intros regs6 R61 R62 R68 R69 R610 K6.
    pose proof (MRx_MRc _ _ _ _ _ CM5) as Mc. pose proof (mc_wf _ _ _ _ _ Mc) as HW.
    destruct (user_blocks_frame A5 q mn HW Hin) as (g & am & idx & fr & Hu & Hidx & Hfr & Hk & Hn & Hp).
    pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
    destruct (meta_in_area A5 g (MUsed am) HW (In_of_mlookup _ _ _ Mg)) as (a & ka & Hain & Hka & Eg).
    destruct (used_group_region [] None U0 A5 g am HW Hu) as (rg & Hrg & Hkd & Hlv & Ho & Hext & _).
    assert (ES6 : spZ regs6 = spZ regs - 32) by (rewrite <- ES; unfold spZ; rewrite R62; reflexivity).
    assert (FP : free_pre (kcase_of am) (rcase_of (reserved_of am fr)) (fv_of regs6 L5 g am idx fr a (rg_len rg)) mem5).
    { apply (free_pre_intro L5 A5 regs6 mem5 md5 g am idx fr a ka rg Mc (MRx_rsv _ _ _ _ _ CM5) Hu Hidx Hfr Hk).
      - rewrite Hn, <- Hp. exact Hin.
      - rewrite R610, H10, <- Hp. reflexivity.
      - rewrite ES6. unfold CALLOC_STACK, ALLOC_STACK in *. lia.
      - intros x Hx. apply Cstk. rewrite ES6 in Hx. exact Hx.
      - exact (conj Hain (conj Hka Eg)).
      - exact (conj Hrg (conj Hkd (conj Hlv (conj Ho Hext)))). }
    eapply SR_bind.
    { refine (az_SR _ _ _ mem5 md5 FP _ Hh Hl).
      change (fv_regs (fv_of regs6 L5 g am idx fr a (rg_len rg))) with regs6. rewrite R61. reflexivity. }
    intros c7 (regs7 & -> & KEEP & AZT).
    change (fv_regs (fv_of regs6 L5 g am idx fr a (rg_len rg))) with regs6 in *.
    rewrite R61.
    assert (R72 : getr regs7 2 = getr regs6 2) by (apply KEEP; left; vm_compute; reflexivity).
    assert (R78 : getr regs7 8 = getr regs6 8) by (apply KEEP; left; vm_compute; reflexivity).
    assert (R79 : getr regs7 9 = getr regs6 9) by (apply KEEP; left; vm_compute; reflexivity).
    assert (K7 : kr regs6 regs7).
    { intros r Hr. apply KEEP.
      assert (Hc : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
                   r = 26 \/ r = 27) by lia.
      repeat (destruct Hc as [Hc|Hc]; [subst r; vm_compute; auto|]); subst r; vm_compute; auto. }
    assert (ES7 : spZ regs7 = spZ regs - 32) by (rewrite <- ES6; unfold spZ; rewrite R72; reflexivity).
    apply (s_azret regs7 mem5 md5 junk (getr regs 1) (getr regs 8) (getr regs 9) _ Hh Hl).
    + rewrite ES7. exact Cfr.
    + intros Hnz7 regs' F2 F8 F9 F10 K'. rewrite (kb_ret_pc _ Cra).
      exists L5, regs', mem5, md5. split; [reflexivity|]. split.
      * refine (kb_post B0 API0 CALLOC_STACK L A regs mem md (fun _ => False) L5 A5 regs' mem5 md5 Cmid _).
        apply (fin_pres regs regs7 regs'); try assumption.
        -- unfold CALLOC_STACK, ALLOC_STACK in *. lia.
        -- rewrite R72, R62. exact Cr2.
        -- exact (kr_trans _ _ _ (kr_trans _ _ _ Ckr K6) K7).
      * cbn [fst snd]. split; [rewrite F10, R78, R68, H10; reflexivity|]. split; [exact HQ0|]. split; [exact HUB|].
        apply AZ. rewrite Hp. apply (az_true_allzero A5 g am idx fr regs6 L5 a (rg_len rg) HW Hu Hidx Hfr).
        apply AZT. intros E. rewrite E in Hnz7. vm_compute in Hnz7. discriminate Hnz7.
    + intros regs8 R82 R88 R89 K8.
      apply (tail_memset L A regs mem md mn L5 A5 regs5 mem5 md5 junk q regs8 C Hin HQ0 HUB).
      * rewrite R82, R72, R62. exact Cr2.
      * rewrite R88, R78, R68. exact H10.
      * rewrite R89, R79, R69. exact Cr9.
      * exact (kr_trans _ _ _ (kr_trans _ _ _ (kr_trans _ _ _ Ckr K6) K7) K8).
Qed.
End a.
Theorem src0_calloc_realizes {fx : YK11.FPState} {rc : YM05.RunCeil} : calloc_realizes src0_msyms (MRx src0_msyms).
Proof.
  intros pc L A regs mem md m n Hpc PRE H10 H11 Hm Hn Hmn RO.
  cbn in Hpc. injection Hpc as <-.
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hlo & Hhi & HSW & Htp & Herr & Haux).
  destruct (mr_model _ _ (MRx_laws src0_msyms) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof alloc_ceiling_value as AC. pose proof errno_low as ERR.
  assert (HMN : bv_unsigned (getr regs 11) * bv_unsigned (getr regs 10) = m * n).
  { rewrite H10, H11, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    destruct (Z.eq_dec n 0) as [->|Hn0]; [rewrite Z.mod_0_l by lia; lia|].
    destruct (Z.eq_dec m 0) as [->|Hm0]; [rewrite Z.mod_0_l by lia; lia|].
    rewrite !Z.mod_small by nia. lia. }
  assert (ST : Frame.stk rsegs mem (spZ regs - 32) (spZ regs)).
  { pose proof (kb_stk B0 API0 img_low0 CALLOC_STACK L A regs mem md PRE ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia)) as S.
    exact (proj2 (Frame.stk_split _ _ (spZ regs - CALLOC_STACK) (spZ regs - 32) (spZ regs) S
                    ltac:(unfold CALLOC_STACK, ALLOC_STACK in *; lia))). }
  eapply mreal_SR_pre with (P := fun c' => mreal (ms_segs src0_msyms) c' (malloc (m * n) A)
                                 (calloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (m * n)));
    [|intros c' Hc; exact Hc].
  apply (s_entry regs mem md (m * n) _ Hh Hl ST HMN ltac:(lia)).
  intros regs1 mem1 junk R1 R2 R4 R8 R9 R10 K1 FR1 MU1 WM1.
  assert (ES1 : spZ regs1 = spZ regs - 32).
  { rewrite (spZ_lit regs1 _ R2) by (unfold CALLOC_STACK, ALLOC_STACK in *; lia). lia. }
  assert (PRE1 : call_pre src0_msyms (MRx src0_msyms) L A regs1 mem1 md).
  { apply (proj2 (call_pre_k_alloc src0_msyms (MRx src0_msyms) L A regs1 mem1 md)).
    refine (kb_pre_A B0 API0 CALLOC_STACK 32 ALLOC_STACK L A regs mem md regs1 mem1 [(spZ regs + -32, spZ regs)] PRE
      _ _ _ _ _ R4 _ MU1 WM1 _ _).
    - lia.
    - unfold ALLOC_STACK. lia.
    - unfold CALLOC_STACK. lia.
    - exact ES1.
    - rewrite ES1. lia.
    - unfold YK0s.ret_ok. rewrite R1. reflexivity.
    - intros x Hx Hle. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [unfold CALLOC_STACK, ALLOC_STACK in *; lia | exact I]. }
  eapply mreal_post.
  { exact (@src0_malloc_realizes fx rc (@src0_alloc_meta fx rc) (@src0_malloc_small fx rc (@src0_alloc_slot fx rc))
             L A regs1 mem1 md (m * n) PRE1 R10 ltac:(nia)). }
  intros r c5 (L5 & regs5 & mem5 & md5 & -> & POST & RES).
  rewrite R1.
  pose proof (proj1 (call_post_k_alloc src0_msyms (MRx src0_msyms) L A regs1 mem1 md _ L5 (snd r) regs5 mem5 md5) POST)
    as POSTk.
  destruct (kb_mid_call B0 API0 ALLOC_STACK L A regs1 mem1 md _ L5 (snd r) regs5 mem5 md5 POSTk) as [MID2 PRES5].
  pose proof POST as (HM5 & _ & _ & _ & _ & _ & _ & HF5 & _ & HSC5).
  pose proof (proj1 PRE1) as HM1.
  assert (MID1 : kb_mid B0 API0 CALLOC_STACK (spZ regs) L A mem md (fun _ => False) L A mem1 md).
  { apply (kb_mid_A B0 API0 img_low0 CALLOC_STACK (spZ regs) L A mem md mem1 [(spZ regs + -32, spZ regs)] (fun _ => False)
      HM HWF HB).
    - intros a [Ha|Ha]; [apply HSW; exact Ha | apply Herr; exact Ha].
    - exact MU1.
    - exact WM1.
    - intros x Hx Hs _. cbn [Frame.outside]. split; [unfold CALLOC_STACK, ALLOC_STACK in Hs; lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [unfold CALLOC_STACK, ALLOC_STACK in *; lia | exact I]. }
  rewrite ES1 in MID2.
  pose proof (kb_mid_seqAX B0 API0 CALLOC_STACK (spZ regs) L A mem md (fun _ => False) mem1 ALLOC_STACK (spZ regs - 32)
    (fun _ => False) L5 (snd r) mem5 md5 MID1 MID2 ltac:(unfold CALLOC_STACK; lia) ltac:(lia) Hlo ltac:(lia)
    ltac:(intros a _ _ F; exact F)) as MID12.
  pose proof (kb_mid_E B0 API0 CALLOC_STACK (spZ regs) L A mem md _ (fun _ => False) L5 (snd r) mem5 md5 MID12
    ltac:(intros a [F|F]; exact F)) as MIDF.
  assert (FR5 : Step.rw_cells rsegs mem5 (spZ regs - 32)
                  [Cells.CB 8 junk; Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)]).
  { replace (spZ regs - 32) with (spZ regs + -32) by lia.
    pose proof (Step.rw_cells_bound _ _ _ _ FR1) as BF. cbn [Cells.cells_size Cells.csize] in BF.
    apply (rw_cells_ext mem1 mem5 _ _ FR1). intros a Ha. cbn [Cells.cells_size Cells.csize] in Ha.
    destruct (HF5 a) as [E W].
    - left. unfold CALLOC_STACK, ALLOC_STACK in *. lia.
    - intros Ho. pose proof (mr_owned_low _ _ (MRx_laws src0_msyms) _ _ _ _ _ HM1 Ho).
      unfold CALLOC_STACK, ALLOC_STACK in *. lia.
    - intros Ho. pose proof (mr_owned_low _ _ (MRx_laws src0_msyms) _ _ _ _ _ HM5 Ho).
      unfold CALLOC_STACK, ALLOC_STACK in *. lia.
    - unfold scratch. rewrite ES1. unfold CALLOC_STACK, ALLOC_STACK in *. lia.
    - tauto.
    - split; [exact E | apply W]. }
  assert (RO5 : MemNorm.ro_agree rsegs mem5).
  { refine (ro_agree_post src0_msyms (MRx src0_msyms) CALLOC_STACK L A regs mem md (fun _ => False) L5 (snd r) regs mem5
      md5 (MRx_AllocExtra src0_msyms) _ Hlo HM _ _ RO).
    - vm_compute. reflexivity.
    - intros a F. destruct F.
    - exact (kb_post B0 API0 CALLOC_STACK L A regs mem md (fun _ => False) L5 (snd r) regs mem5 md5 MIDF
               (fun r0 _ => eq_refl)). }
  assert (C : ctx5 L A regs mem md (m * n) L5 (snd r) regs5 mem5 md5 junk).
  { split.
    - nia.
    - exact Hra.
    - split; [exact Hal | split; [exact Hlo | exact Hhi]].
    - exact MIDF.
    - exact HM5.
    - intros x Hx. apply HSC5. left. rewrite ES1. lia.
    - exact FR5.
    - transitivity (getr regs1 2); [exact (PRES5 2 ltac:(unfold callee_saved; lia)) |].
      rewrite R2. f_equal; lia.
    - transitivity (getr regs1 8); [exact (PRES5 8 ltac:(unfold callee_saved; lia)) | exact R8].
    - transitivity (getr regs1 9); [exact (PRES5 9 ltac:(unfold callee_saved; lia)) | exact R9].
    - exact (kr_trans _ _ _ K1 (kr_pres _ _ PRES5)).
    - exact RO5. }
  destruct r as [[q|] A5]; cbn [fst snd] in *.
  - destruct RES as (H105 & HQ0 & HUB & AZ).
    exact (leaf_some L A regs mem md (m * n) L5 A5 regs5 mem5 md5 junk q C H105 HQ0 HUB AZ).
  - destruct RES as (H105 & UB).
    exact (leaf_null L A regs mem md (m * n) L5 A5 regs5 mem5 md5 junk C H105 UB).
Qed.
