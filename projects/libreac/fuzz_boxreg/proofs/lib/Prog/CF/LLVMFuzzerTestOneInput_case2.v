From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregRd bcmp_c reac_boxreg_find_c reac_boxreg_find
  bcmp.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

Lemma c2_cells_mid : forall m A pre c post,
  rw_cells rsegs m A (pre ++ c :: post) -> bytes_at rsegs m (A + Z.of_nat (cells_size pre)) (cbytes c).
Proof.
  intros m A pre c post [[Hwf Hb] _].
  apply cells_wf_app in Hwf. destruct Hwf as [Hw1 _].
  rewrite cells_bytes_app in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hw1.
  cbn [cells_bytes] in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

Lemma c2_cb_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[HWF HBY] _]. cbn [cells_wf cell_wf] in HWF. destruct HWF as [HL _].
  cbn [cells_bytes cbytes] in HBY. rewrite app_nil_r in HBY. split; assumption.
Qed.

Lemma c2_mac_at : forall m A j0 fw j1 pv M jx w1 w2,
  rw_cells rsegs m A [CB 8 j0; C8 fw; CB 16 j1; CB 288 pv; CB 6 M; CB 2 jx; C8 w1; C8 w2] ->
  bytes_at rsegs m (A + 320) M /\ length M = 6%nat.
Proof.
  intros m A j0 fw j1 pv M jx w1 w2 H. split.
  - exact (c2_cells_mid m A [CB 8 j0; C8 fw; CB 16 j1; CB 288 pv] (CB 6 M) [CB 2 jx; C8 w1; C8 w2] H).
  - destruct H as [[HWF _] _]. cbn [cells_wf cell_wf] in HWF. tauto.
Qed.

Lemma c2_merge_mac : forall m A j0 fw j1 pv M jx w1 w2,
  rw_cells rsegs m A [CB 8 j0; C8 fw; CB 16 j1; CB 288 pv; CB 6 M; CB 2 jx; C8 w1; C8 w2] ->
  rw_cells rsegs m A [CB 8 j0; C8 fw; CB 16 j1; CB 288 pv; CB 8 (M ++ jx); C8 w1; C8 w2].
Proof.
  intros m A j0 fw j1 pv M jx w1 w2 H.
  pose proof (rw_cells_merge rsegs m A [CB 8 j0; C8 fw; CB 16 j1; CB 288 pv] [CB 6 M; CB 2 jx] [C8 w1; C8 w2] H) as H'.
  cbn [cells_size cells_bytes cbytes csize Nat.add app] in H'. rewrite app_nil_r in H'. exact H'.
Qed.

Lemma c2_merge6 : forall m A j0 fw j1 pv mid post,
  rw_cells rsegs m A ([CB 8 j0; C8 fw; CB 16 j1; CB 288 pv] ++ mid ++ post) -> cells_size mid = 6%nat ->
  rw_cells rsegs m A ([CB 8 j0; C8 fw; CB 16 j1; CB 288 pv] ++ CB 6 (cells_bytes mid) :: post).
Proof.
  intros m A j0 fw j1 pv mid post H E. pose proof (rw_cells_merge rsegs m A _ mid post H) as H'.
  rewrite E in H'. exact H'.
Qed.

Lemma c2_bv : forall m A bs (w : word), bytes_at rsegs m A bs -> w = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
  bytes_at rsegs m (bv_unsigned w) bs.
Proof. intros m A bs w H -> HA. rewrite unsigned_lit by lia. exact H. Qed.

Lemma c2_zero_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10392 zero6.
Proof.
  intros m MI. apply ro_bytes_at; [ exact MI | lia | cbn; lia | ].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma c2_memcmp_eq : forall l, length l = 6%nat -> memcmp_model l l 6 = Some 0.
Proof.
  intros l L. destruct (memcmp_model_total l l 6 ltac:(lia) ltac:(lia)) as [v Hv].
  destruct (fnd_memcmp 6 l l v L L Hv) as [_ Iv]. rewrite Hv. f_equal. apply Iv. reflexivity.
Qed.

Lemma c2_cb_mk : forall m A bs n, bytes_at rsegs m A bs -> length bs = n -> wr_at rsegs m A (Z.of_nat n) ->
  rw_cells rsegs m A [CB n bs].
Proof.
  intros m A bs n HB HL HW. split; [ split | ].
  - cbn [cells_wf cell_wf]. split; [ exact HL | exact I ].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma c2_idx : forall r z, 0 <= z < 6 ->
  Z_to_bv 64 (r + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 6)) -
                   bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 3)))) = Z_to_bv 64 (r + 56 * z).
Proof.
  intros r z Hz. rewrite (unsigned_lit z) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Ltac c2_killz H :=
  exfalso; zify_cond H; rewrite ?unsigned_lit_wrap, ?signed_lit in H by lia;
  first [ lia | Z.div_mod_to_equations; lia ].

Ltac c2_killc H := exfalso; vm_compute in H; discriminate H.

Ltac c2_post := match goal with HMI : mem_inv rsegs ?mm |- _ => post_call rsegs mm end.

Ltac c2_zcall BC M HM :=
  let v := fresh "v" in let Hv := fresh "Hv" in let Rv := fresh "Rv" in let Iv := fresh "Iv" in
  destruct (memcmp_model_total M zero6 6 ltac:(lia) ltac:(cbn; lia)) as [v Hv];
  destruct (fnd_memcmp 6 M zero6 v ltac:(lia) eq_refl Hv) as [Rv Iv];
  eapply evt_cut;
  [ eapply BC with (ls := M) (rs := zero6) (v := v);
    [ eapply c2_bv; [ exact HM | fnd_eq | lia ]
    | eapply c2_bv; [ apply c2_zero_at; assumption | fnd_eq | lia ]
    | change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat; exact Hv | assumption ]
  | c2_post ].

Ltac c2_end ip' inn' M jx :=
  apply evt_done;
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mm _) => exists mm, ip', inn', (M ++ jx) end;
  do 20 eexists; split; [ reflexivity | ];
  split; [ first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] | ];
  split; [ assumption | ]; split; [ assumption | ]; split; [ assumption | ]; split; [ assumption | ];
  split; [ apply c2_merge_mac; assumption | ];
  split; [ apply c2_cb_mk; assumption | ];
  split; [ lia | split; lia ].

Definition c2_Q (sp gp tp s0 s4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo r : Z) (bs j0 : list byte) (fw : word) (j1 pv : list byte) (ip0 tot : Z)
    (ms' : machine_state) : Prop :=
  exists (m' : word -> option byte) (ip' inn' : Z) (jm' : list byte)
         (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s5' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4 s5' s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (Z_to_bv 64 0x13314) fc None m' (seg_rom rsegs) /\
    s3' = Z_to_bv 64 4294967295 /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp + 344)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' (bv_unsigned sp)
      [CB 8 j0; C8 fw; CB 16 j1; CB 288 pv; CB 8 jm'; C8 (Z_to_bv 64 ip'); C8 (Z_to_bv 64 inn')] /\
    rw_cells rsegs m' r [CB 288 bs] /\ ip0 <= ip' /\ 0 <= inn' /\ ip' + inn' = tot.

Lemma c2_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (lo r ip0 tot ip' inn' : Z)
         (bs M jx j0 j1 pv : list byte) (fw : word),
    reac_boxreg_find_contract -> bcmp_contract ->
    s0 = Z_to_bv 64 r ->
    rw_cells rsegs m1 (bv_unsigned sp)
      [CB 8 j0; C8 fw; CB 16 j1; CB 288 pv; CB 6 M; CB 2 jx; C8 (Z_to_bv 64 ip'); C8 (Z_to_bv 64 inn')] ->
    rw_cells rsegs m1 r [CB 288 bs] -> boxreg_B1 bs -> 0 <= r -> r + 288 <= lo ->
    stk rsegs m1 lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp + 344 < 2 ^ 63 ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp + 344)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    ip0 <= ip' -> 0 <= inn' -> ip' + inn' = tot ->
    evt rsegs (c2_Q sp gp tp s0 s4 s6 s7 s8 s9 s10 s11 F fc m lo r bs j0 fw j1 pv ip0 tot)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f90) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m1 lo r ip0 tot ip' inn' bs M jx j0 j1 pv fw FIND BC E0 HS HR B1 R0 Hr ST LO SPB MU WM MI Hip Hinn Htot.
  unfold reac_boxreg_find_contract, REAC_BOXREG_FIND, REAC_BOXREG_FIND_FRAME in FIND.
  unfold bcmp_contract, BCMP in BC.
  subst s0.
  destruct (c2_cb_bytes _ _ _ _ HR) as [HB HL].
  destruct HR as [_ HW]. change (Z.of_nat (cells_size [CB 288 bs])) with 288 in HW.
  destruct (c2_mac_at _ _ _ _ _ _ _ _ _ _ HS) as [HM LM].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  unfold boxreg_B1 in B1.
  step. step. step.
  eapply evt_cut.
  { eapply FIND with (lo := lo) (r := r) (p := bv_unsigned sp + 320) (bs := bs) (M := M);
      [ reflexivity | reflexivity | exact HB | exact HL | exact B1 | exact HM | exact LM | exact ST
      | lia | lia | lia | exact MI ]. }
  post_call rsegs m1.
  match goal with H : exists z, _ = Z_to_bv 64 z /\ find_result _ _ z |- _ => destruct H as (z & Ez & FRz) end.
  match type of Ez with ?x = _ => subst x end.
  assert (Zb : -1 <= z < bx_n bs).
  { destruct FRz as [[_ ->] | [[_ (Hz & _ & _)] | (_ & -> & _)]]; lia. }
  pose proof (rd4_bytes_at _ r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as BN.
  change (rd4 bs 280) with (bx_n bs) in BN.
  pose proof (fnd_rd4 _ _ _ BN) as RN.
  step. step. step.
  if_cases HC1; [ c2_killz HC1 | ].
  step. step. rewrite ?fnd_sx32 by lia.
  if_cases HC2; [ c2_killz HC2 | ].
  step.
  if_cases HC3; zify_cond HC3; rewrite ?signed_lit in HC3 by lia.
  - assert (Ez : z = -1) by lia. subst z.
    do 5 step.
    c2_zcall BC M HM.
    step. step. step.
    if_cases HC4; [ | c2_killc HC4 ].
    c2_end ip' inn' M jx.
  - destruct FRz as [[_ E] | [[NZ (Hz & Hmac & _)] | (_ & E & _)]]; [ lia | | lia ].
    pose proof (bytes_at_bsub _ r bs (56 * z) 6 HB ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as HBi.
    change (bsub bs (56 * z) 6) with (bx_mac bs z) in HBi. rewrite Hmac in HBi.
    do 7 step.
    eapply evt_cut.
    { eapply BC with (ls := M) (rs := M) (v := 0);
        [ eapply c2_bv; [ exact HBi | apply c2_idx; lia | lia ] | eapply c2_bv; [ exact HM | fnd_eq | lia ]
        | change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat; apply c2_memcmp_eq; exact LM | assumption ]. }
    c2_post.
    step.
    if_cases HC5; [ c2_killc HC5 | ].
    do 5 step.
    c2_zcall BC M HM.
    step. step. step.
    if_cases HC4; [ c2_killz HC4 | ].
    step.
    if_cases HC6; [ | ].
    + exfalso. zify_cond HC6. rewrite ?unsigned_lit_wrap in HC6.
      match goal with Rv : -256 < ?v < 256, Iv : ?v = 0 <-> _ |- _ =>
        assert (V : v = 0) by (clear - HC6 Rv; Z.div_mod_to_equations; lia); apply Iv in V; exact (NZ V) end.
    + step. c2_end ip' inn' M jx.
Qed.

Lemma c2_kept : forall bs, llvm_kept bs bs (-1).
Proof. intros bs j Hj. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; right; reflexivity. Qed.

Ltac c2_go FIND BC E0 HS HR B1 ST MU WM MI :=
  let HM := fresh "HM" in
  rd_m6 HS HM;
  eapply c2_tail; [ exact FIND | exact BC | exact E0 | exact HM | exact HR | exact B1 | lia | lia | exact ST
                  | lia | lia | exact MU | exact WM | exact MI | lia | lia | lia ].

Lemma c2_head :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo r fab ip inn e : Z)
         (j0 j1 jm bs rest : list byte),
    reac_boxreg_find_contract -> bcmp_contract ->
    s0 = Z_to_bv 64 r -> s1 = Z_to_bv 64 ip -> s2 = Z_to_bv 64 (inn - 1) -> s3 = Z_to_bv 64 (ip + 1) ->
    s5 = Z_to_bv 64 inn -> s9 = Z_to_bv 64 (bv_unsigned sp + 326) ->
    rw_cells rsegs m (bv_unsigned sp)
      [CB 8 j0; C8 (Z_to_bv 64 fab); CB 16 j1; CB 288 bs; CB 8 jm; C8 (Z_to_bv 64 (ip + 1));
       C8 (Z_to_bv 64 (inn - 1))] ->
    rw_cells rsegs m r [CB 288 bs] -> boxreg_inv bs ->
    bytes_at rsegs m (ip + 1) rest -> Z.of_nat (length rest) = inn - 1 ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    bv_unsigned sp + 448 <= 2 ^ 47 -> 0 <= r -> r + 288 <= lo -> 0 <= ip -> ip + inn = e -> e <= lo -> 1 <= inn ->
    evt rsegs (c2_Q sp gp tp s0 s4 s6 s7 s8 s9 s10 s11 F fc m lo r bs j0 (Z_to_bv 64 fab) j1 bs ip e)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12da8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo r fab ip inn e j0 j1 jm bs rest FIND BC E0 E1 E2 E3 E5 E9 HS HR HI HP HL MI ST LO SPB Hr0 Hr Hip Hie
    Hel Hinn.
  subst s1 s2 s3 s5 s9.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp + 344)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof HI as ((_ & B1 & _) & _).
  step. step. sg_br HC; clear HC.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x12e24) _ _ _ _) =>
           destruct rest as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 rest]]]]]]; cbn [length] in HL;
           rd_go 0x12e2c 0x12f90; c2_go FIND BC E0 HS HR B1 ST MU WM MI
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x12db0) _ _ _ _) =>
           destruct rest as [|x0 rest]; cbn [length] in HL;
           rd_go 0x12dc4 0x12f90; c2_go FIND BC E0 HS HR B1 ST MU WM MI
       end.
Qed.

Lemma c2_evt : reac_boxreg_find_contract -> bcmp_contract -> llvm_case_evt (llvm_case_pc 2).
Proof.
  intros FIND_C BCMP_C F fc regs mem spv lo r fab ip inn op i e gp tp j0 j1 jm bs rest E2 E3 E4 E8 E9 E18 E19 E21
    E22 E23 E24 E25 E26 E27 HS HR HI HF HP HL MI ST Hlo Hlo2 Hsp Hr4 Hr16 Hr Hip Hie Hel Hinn Hinn2 Hop Hi.
  change (llvm_case_pc 2) with 0x12da8.
  unfold Regs6ss.mkR_of.
  assert (Hspv : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  assert (G2 : reg_get regs 2 = Z_to_bv 64 spv) by exact E2.
  assert (G3 : reg_get regs 3 = gp) by exact E3.
  assert (G4 : reg_get regs 4 = tp) by exact E4.
  assert (G8 : reg_get regs 8 = Z_to_bv 64 r) by exact E8.
  assert (G9 : reg_get regs 9 = Z_to_bv 64 ip) by exact E9.
  assert (G18 : reg_get regs 18 = Z_to_bv 64 (inn - 1)) by exact E18.
  assert (G19 : reg_get regs 19 = Z_to_bv 64 (ip + 1)) by exact E19.
  assert (G21 : reg_get regs 21 = Z_to_bv 64 inn) by exact E21.
  assert (G24 : reg_get regs 24 = Z_to_bv 64 i) by exact E24.
  assert (G25 : reg_get regs 25 = Z_to_bv 64 (spv + 326)) by exact E25.
  assert (G26 : reg_get regs 26 = Z_to_bv 64 (spv + 32)) by exact E26.
  assert (G27 : reg_get regs 27 = Z_to_bv 64 fab) by exact E27.
  rewrite G2, G3, G4, G8, G9, G18, G19, G21, G24, G25, G26, G27.
  eapply evt_mono.
  - eapply c2_head with (lo := lo) (r := r) (fab := fab) (ip := ip) (inn := inn) (e := e) (j0 := j0) (j1 := j1)
      (jm := jm) (bs := bs) (rest := rest);
      first [ exact FIND_C | exact BCMP_C | reflexivity | exact HR | exact HI | exact HP | exact HL | exact MI
            | (rewrite Hspv; first [ reflexivity | exact HS | exact ST | lia ]) | lia ].
  - intros ms' HQ. unfold c2_Q in HQ.
    destruct HQ as (m' & ip' & inn' & jm' & ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' &
      a7' & s2' & s3' & s5' & t3' & t4' & t5' & t6' & -> & Es3 & MU & WM & MI' & ST' & HS' & HR' & Hip' & Hinn' &
      Htot).
    subst s3'. rewrite Hspv in MU, HS'.
    unfold llvm_case_Q. rewrite Hspv.
    do 22 eexists. exists m', j1, jm', ip', inn', bs. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; intros x (H1 & H2 & _); split; [lia | exact I]|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact HS'|].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact (proj1 (c2_cb_bytes _ _ _ _ HR'))|]. split; [exact (proj2 HR')|].
    split; [exact HI|]. split; [exact HF|]. exact (c2_kept bs).
Qed.

Section C2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Theorem llvm_case2_ok : llvm_case_ok B API 2.
Proof. exact (llvm_case_of_evt B API 2 (c2_evt (reac_boxreg_find_holds bcmp_holds) bcmp_holds)). Qed.

End C2.
