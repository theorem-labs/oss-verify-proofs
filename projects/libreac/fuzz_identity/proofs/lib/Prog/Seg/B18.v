From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb3.
Import ListNotations.
Open Scope Z_scope.

Lemma b18_fw : forall inp i, rec_r inp i = 0 -> rec_addr inp i = 0 -> 4 <= rec_k inp i ->
  bz (nthb (rec_pl inp i) 0) <= 9 -> bz (nthb (rec_pl inp i) 1) <= 9 -> bz (nthb (rec_pl inp i) 2) <= 9 ->
  9 < bz (nthb (rec_pl inp i) 3).
Proof.
  intros inp i Hr Ha Hk H0 H1 H2.
  destruct (Z_lt_le_dec 9 (bz (nthb (rec_pl inp i) 3))) as [H|H3]; [exact H|]. exfalso.
  pose proof (rec_pl_length inp i) as Hl. unfold rec_r in Hr. rewrite Ha in Hr.
  revert Hl H0 H1 H2 H3 Hr. generalize (rec_pl inp i) as p. intros p Hl H0 H1 H2 H3 Hr.
  assert (E : ((4 <=? length p)%nat && all_digits (firstn 4 p))%bool = true).
  { destruct p as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in Hl; try lia.
    unfold nthb in *. cbn [nth] in *. unfold all_digits. cbn [firstn forallb length Nat.leb].
    rewrite (proj2 (Z.leb_le _ _) H0), (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2),
      (proj2 (Z.leb_le _ _) H3). reflexivity. }
  unfold ING in Hr. change (0 =? ADDR_FIRMWARE) with true in Hr. cbv beta iota in Hr.
  unfold ing_firmware in Hr. rewrite E in Hr. cbn [fst] in Hr. discriminate Hr.
Qed.

Lemma b18_name : forall inp i, rec_r inp i = 0 -> rec_addr inp i = ADDR_MODEL_NAME -> 2 <= rec_k inp i ->
  bz (nthb (rec_pl inp i) 1) = 0.
Proof.
  intros inp i Hr Ha Hk. pose proof (rec_pl_length inp i) as Hl. unfold rec_r in Hr. rewrite Ha in Hr.
  revert Hl Hr. generalize (rec_pl inp i) as p. intros p Hl Hr.
  destruct p as [|b0 [|b1 r]]; cbn [length] in Hl; try lia.
  unfold nthb. cbn [nth].
  destruct (Z.eqb_spec (bz b1) 0) as [E|E]; [exact E|]. exfalso.
  assert (W : (1 <= name_len (b0 :: b1 :: r))%nat).
  { unfold name_len, NAME_CAP. cbn [length skipn].
    replace (S (S (length r)) - 1)%nat with (S (length r)) by lia.
    replace (Nat.min (S (length r)) (17 - 1)) with (S (Nat.min (length r) 15)) by lia.
    cbn [firstn first_zero]. rewrite (proj2 (Z.eqb_neq _ _) E). lia. }
  unfold ING in Hr. change (ADDR_MODEL_NAME =? ADDR_FIRMWARE) with false in Hr.
  change (ADDR_MODEL_NAME =? ADDR_MODEL_NAME) with true in Hr. cbv beta iota in Hr.
  unfold ing_name in Hr. cbv zeta in Hr.
  rewrite (proj2 (Nat.leb_le 1 _) W) in Hr. cbn [length Nat.leb andb fst] in Hr. discriminate Hr.
Qed.

Ltac b18_fin :=
  apply Exec.evt_done; eexists _, _; split; [reflexivity|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|];
  split; [apply munch_refl|]; split; [apply wmono_refl|]; apply Forall_nil.

Ltac b18_side := first [ lia | match goal with |- context [@bv_unsigned 8 ?b] => pose proof (tb_byte_range b); lia end ].

Ltac b18_cmp := rewrite ?tb_eqb_lit, ?tb_ltu_lit by b18_side.

Ltac b18_tail a k Hr0 RD1 :=
  step; step; b18_cmp;
  destruct (Z.eqb_spec a 4096) as [Hn|Hn]; cbn [negb];
  [ step; step; b18_cmp;
    destruct (Z.ltb_spec k 2) as [Hk2|Hk2];
    [ b18_fin
    | let R1 := fresh "R1" in let Hz := fresh "Hz" in pose proof (RD1 ltac:(lia)) as R1;
      change (Z.to_nat 1) with 1%nat in R1;
      pose proof (b18_name _ _ Hr0 Hn ltac:(lia)) as Hz; unfold bz in Hz;
      step; step; unfold zxb; b18_cmp; rewrite Hz; cbn [Z.eqb negb]; b18_fin ]
  | b18_fin ].

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_B18 : forall i,
  Hrec B APIf ra (Inv_K134c8_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K1329c_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x1329c 0x134c8 _ _ _
    (fun regs m => Z.of_nat i < NR g /\ getr regs 19 = Z_to_bv 64 (Z.of_nat i) /\ NRb g m /\ G16 g m /\
       HWb g (S i) m /\ IDb g (S i) m /\
       getr regs 20 = Z_to_bv 64 (g_p g + rec_body (g_in g) i) /\ getr regs 21 = Z_to_bv 64 (rec_k (g_in g) i) /\
       getr regs 18 = Z_to_bv 64 (rec_Lp (g_in g) i) /\ getr regs 22 = Z_to_bv 64 pl) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as ((HREC & E21 & E20 & E22 & HPL & HID & HAG & HBF & HLP) & E23 & (E27 & E8 & E18 & E24 & E25 & E26) &
    E9 & Hr0 & E10).
  pose proof HREC as (Hi & E19 & HNR & HG16 & HHW).
  pose proof HF as (HGV & E2 & E3 & E4 & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSc & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  destruct (tb_norm_frame B APIf ra empty FF g _ _ _ _ _ _ _ HF) as (HRO & MIn & WRn & STn).
  exists [], ([(19%bv, Z_to_bv 64 (Z.of_nat i)); (20%bv, Z_to_bv 64 (g_p g + rec_body (g_in g) i));
    (21%bv, Z_to_bv 64 (rec_k (g_in g) i)); (18%bv, Z_to_bv 64 (rec_Lp (g_in g) i)); (22%bv, Z_to_bv 64 pl)]
    : list (reg * word)), [].
  split; [intros x H; exfalso; apply H; exact I|].
  split.
  - pose proof (tb_addr_range (g_in g) i) as Har. pose proof (rec_k_range (g_in g) i) as Hkr.
    pose proof (rec_pl_length (g_in g) i) as Hpl.
    unfold PLB in HPL. pose proof (bytes_at_bound rsegs _ _ _ HPL) as Hplb. rewrite Hpl in Hplb.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HPL) as HPLn.
    unfold LPm, q64, spk, fsp, SLOT_FRAME in HLP. pose proof (tb_rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HLP)) as RD40.
    unfold rmk. rewrite E2, E3, E4, E19, E21, E20, E22, E23, E10.
    unfold fsp, SLOT_FRAME in *. unfold SLOT_K, SLOT_STACK in *.
    assert (RD : forall j, 0 <= j < rec_k (g_in g) i ->
      ov_read_bytes rsegs (normalize rsegs mem) (wa (pl + j)) 1 = Some [nthb (rec_pl (g_in g) i) (Z.to_nat j)]).
    { intros j Hj. apply tb_rd1; [exact HPLn | lia | rewrite Hpl; lia]. }
    step. if_false. step. step.
    step. b18_cmp.
    destruct (Z.eqb_spec (rec_addr (g_in g) i) 0) as [Ha|Ha]; cbn [negb].
    + step. step. b18_cmp.
      destruct (Z.ltb_spec (rec_k (g_in g) i) 4) as [Hk|Hk].
      * step. step. b18_cmp. replace (rec_addr (g_in g) i =? 1536) with false by (rewrite Ha; reflexivity).
        cbn [negb].
        b18_tail (rec_addr (g_in g) i) (rec_k (g_in g) i) Hr0 (RD 1).
      * pose proof (RD 0 ltac:(lia)) as R0. pose proof (RD 1 ltac:(lia)) as R1.
        pose proof (RD 2 ltac:(lia)) as R2. pose proof (RD 3 ltac:(lia)) as R3.
        change (Z.to_nat 0) with 0%nat in R0. change (Z.to_nat 1) with 1%nat in R1.
        change (Z.to_nat 2) with 2%nat in R2. change (Z.to_nat 3) with 3%nat in R3.
        step. step. unfold zxb. b18_cmp.
        destruct (Z.ltb_spec 9 (bv_unsigned (nthb (rec_pl (g_in g) i) 0))) as [P0|P0]; [b18_fin|].
        step. step. unfold zxb. b18_cmp.
        destruct (Z.ltb_spec 9 (bv_unsigned (nthb (rec_pl (g_in g) i) 1))) as [P1|P1]; [b18_fin|].
        step. step. unfold zxb. b18_cmp.
        destruct (Z.ltb_spec 9 (bv_unsigned (nthb (rec_pl (g_in g) i) 2))) as [P2|P2]; [b18_fin|].
        step. step. unfold zxb. b18_cmp.
        pose proof (b18_fw _ _ Hr0 Ha Hk P0 P1 P2) as P3. unfold bz in P3.
        rewrite (proj2 (Z.ltb_lt _ _) P3). cbn [negb].
        step. b18_fin.
    + step. step. b18_cmp.
      destruct (Z.eqb_spec (rec_addr (g_in g) i) 1536) as [H6|H6]; cbn [negb].
      * assert (K8 : rec_k (g_in g) i < 8).
        { pose proof Hr0 as Hr0'. unfold rec_r in Hr0'. rewrite H6 in Hr0'.
          pose proof (tb_ing0_ver _ _ Hr0'). lia. }
        step. step. b18_cmp. rewrite (proj2 (Z.ltb_lt _ _) K8). cbn [negb].
        b18_tail (rec_addr (g_in g) i) (rec_k (g_in g) i) Hr0 (RD 1).
      * b18_tail (rec_addr (g_in g) i) (rec_k (g_in g) i) Hr0 (RD 1).
  - intros regs' mem' HRL MU _. tb_regs HRL.
    unfold NRb, G16, HWb, IDb in *. unfold q64, u32 in *.
    destruct HHW as (HW1 & HW2 & HW3).
    unfold rec_have, rec_hwb. rewrite (tb_rec_hw_r0 _ _ Hr0).
    fold (rec_have (g_in g) i). fold (rec_hwb (g_in g) i).
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
