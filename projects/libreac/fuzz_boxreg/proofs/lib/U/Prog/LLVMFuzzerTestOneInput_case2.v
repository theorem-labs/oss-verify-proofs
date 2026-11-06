From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd bcmp_c reac_boxreg_find_c reac_boxreg_find
  bcmp read_mac_c read_mac memcpy mac_is_zero.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_top
  LLVMFuzzerTestOneInput_seg.
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

Lemma c2_split3 : forall m A c1 c2 c3 n1 n2, rw_cells rsegs m A (c1 ++ c2 ++ c3) ->
  Z.of_nat (cells_size c1) = n1 -> Z.of_nat (cells_size c2) = n2 ->
  rw_cells rsegs m A c1 /\ rw_cells rsegs m (A + n1) c2 /\ rw_cells rsegs m (A + n1 + n2) c3.
Proof.
  intros m A c1 c2 c3 n1 n2 H E1 E2.
  destruct (top_rwc_split m A c1 _ H) as [H1 H23]. rewrite E1 in H23.
  destruct (top_rwc_split m (A + n1) c2 _ H23) as [H2 H3]. rewrite E2 in H3.
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma c2_join3 : forall m A c1 c2 c3 n1 n2,
  rw_cells rsegs m A c1 -> rw_cells rsegs m (A + n1) c2 -> rw_cells rsegs m (A + n1 + n2) c3 ->
  Z.of_nat (cells_size c1) = n1 -> Z.of_nat (cells_size c2) = n2 -> rw_cells rsegs m A (c1 ++ c2 ++ c3).
Proof.
  intros m A c1 c2 c3 n1 n2 H1 H2 H3 E1 E2.
  apply (top_rwc_join m A c1 _ (A + n1)); [exact H1 | lia |].
  apply (top_rwc_join m (A + n1) c2 _ (A + n1 + n2)); [exact H2 | lia | exact H3].
Qed.

Lemma c2_mac8 : forall m A j0 z0 fw j1 iw nw pv ja M w1 w2,
  rw_cells rsegs m A ([CB 8 j0; C8 z0; C8 fw; CB 8 j1; C8 iw; C8 nw; CB 288 pv; CB 2 ja] ++ [CB 6 M] ++ [C8 w1; C8 w2]) ->
  rw_cells rsegs m A [CB 8 j0; C8 z0; C8 fw; CB 8 j1; C8 iw; C8 nw; CB 288 pv; CB 8 (ja ++ M); C8 w1; C8 w2].
Proof.
  intros m A j0 z0 fw j1 iw nw pv ja M w1 w2 H.
  pose proof (rw_cells_merge rsegs m A [CB 8 j0; C8 z0; C8 fw; CB 8 j1; C8 iw; C8 nw; CB 288 pv] [CB 2 ja; CB 6 M]
    [C8 w1; C8 w2] H) as H'.
  cbn [cells_size cells_bytes cbytes csize Nat.add app] in H'. rewrite app_nil_r in H'. exact H'.
Qed.

Lemma c2_used : forall f n, 0 <= n -> 0 <= read_mac_used f n <= n.
Proof. intros f n Hn. unfold read_mac_used. destruct (bv_unsigned f =? 0); lia. Qed.

Lemma c2_m56 : forall z, 0 <= z < 2 ^ 32 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 6)) -
              bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 3))) = Z_to_bv 64 (56 * z).
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !unsigned_lit by lia. f_equal. lia.
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

Lemma c2_kept : forall bs, llvm_kept bs bs (-1).
Proof. intros bs j Hj. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; right; reflexivity. Qed.

Ltac c2_end :=
  apply evt_done; unfold llvm_case_Q;
  lazymatch goal with Hs : bv_unsigned (Z_to_bv 64 ?s) = ?s |- _ => rewrite Hs end;
  do 23 eexists; eexists; do 6 eexists;
  split; [ reflexivity | ];
  split; [ first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] | ];
  split; [ reflexivity | ]; split; [ reflexivity | ];
  split; [ eassumption | ]; split; [ eassumption | ]; split; [ eassumption | ];
  split; [ eassumption | ];
  split; [ lia | ]; split; [ lia | ]; split; [ lia | ];
  split; [ eassumption | ];
  split; [ match goal with H : rw_cells rsegs _ _ [CB 288 _] |- _ => exact (proj2 H) end | ];
  split; [ eassumption | ]; split; [ eassumption | ];
  apply c2_kept.

Lemma c2_evt : read_mac_contract -> reac_boxreg_find_contract -> bcmp_contract -> llvm_case_evt (llvm_case_pc 2).
Proof.
  intros RM FIND BC F fc regs mem spv lo r fab ip inn op i e gp tp j0 j1 jm bs rest E2 E3 E4 E8 E9 E18 E19 E20 E21
    E22 E23 E24 E25 E26 E27 HS HR HI HF HP HL MI ST Hlo Hlo2 Hsp Hspa Hr4 Hr16 Hr Hip Hie Hel Hinn Hinn2 Hop Hi.
  change (llvm_case_pc 2) with 0x12e40.
  unfold Regs6ss.mkR_of.
  assert (G2 : reg_get regs 2 = Z_to_bv 64 spv) by exact E2.
  assert (G3 : reg_get regs 3 = gp) by exact E3.
  assert (G4 : reg_get regs 4 = tp) by exact E4.
  assert (G8 : reg_get regs 8 = Z_to_bv 64 r) by exact E8.
  assert (G9 : reg_get regs 9 = Z_to_bv 64 op) by exact E9.
  assert (G18 : reg_get regs 18 = Z_to_bv 64 inn) by exact E18.
  assert (G19 : reg_get regs 19 = Z_to_bv 64 (ip + 1)) by exact E19.
  assert (G20 : reg_get regs 20 = Z_to_bv 64 ip) by exact E20.
  assert (G21 : reg_get regs 21 = Z_to_bv 64 (inn - 1)) by exact E21.
  assert (G22 : reg_get regs 22 = Z_to_bv 64 1) by exact E22.
  assert (G23 : reg_get regs 23 = Z_to_bv 64 fab) by exact E23.
  assert (G24 : reg_get regs 24 = Z_to_bv 64 (-1 - (spv + 48))) by exact E24.
  assert (G25 : reg_get regs 25 = Z_to_bv 64 (-1 - r)) by exact E25.
  assert (G26 : reg_get regs 26 = Z_to_bv 64 (spv + 48)) by exact E26.
  assert (G27 : reg_get regs 27 = Z_to_bv 64 336) by exact E27.
  rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27.
  clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27.
  unfold read_mac_contract, READ_MAC, READ_MAC_FRAME in RM.
  unfold reac_boxreg_find_contract, REAC_BOXREG_FIND, REAC_BOXREG_FIND_FRAME in FIND.
  unfold bcmp_contract, BCMP in BC.
  assert (Hspv : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  pose proof (munch_refl [(lo, spv + 360); (r, r + 288)] mem) as MU.
  pose proof (wmono_refl rsegs mem) as WM.
  pose proof HI as ((Lbs & B1 & _) & _).
  unfold boxreg_B1 in B1.
  destruct (c2_cb_bytes _ _ _ _ HR) as [HB _].
  lazymatch type of HS with rw_cells _ _ _ ?cs => split_for_access HS rsegs mem spv cs 338%nat 6%nat end.
  lazymatch type of HS with
  | rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; CB 2 ?ja; CB 6 ?jb; ?c9; ?c10] =>
      destruct (c2_split3 mem spv [c0; c1; c2; c3; c4; c5; c6; CB 2 ja] [CB 6 jb] [c9; c10] 338 6 HS
        eq_refl eq_refl) as (HS1 & HS2 & HS3);
      clear HS;
      replace (spv + 338 + 6) with (spv + 344) in HS3 by lia;
      step; step; step; step;
      eapply evt_cut;
      [ eapply RM with (lo := lo) (c := spv + 344) (p := ip + 1) (n := inn - 1) (mac := spv + 338) (pl := rest)
          (junk := jb);
        [ fnd_eq | fnd_eq | clear - Hspa; Z.div_mod_to_equations; lia | exact HS3 | exact HS2 | exact HP | exact HL
        | lia | exact MI | rewrite Hspv; exact ST | rewrite Hspv; lia
        | unfold apart; lia | unfold apart; lia | unfold apart; lia | unfold apart, MAC_BASE; unfold LF_RES_TOP in Hlo; lia
        | rewrite Hspv; unfold apart; lia | rewrite Hspv; unfold apart; lia | rewrite Hspv; unfold apart; lia ] | ]
  end.
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1
    & E & MU1 & WM1 & ST1 & MI1 & HC1 & HM1).
  subst ms'.
  c1_retpc.
  rewrite Hspv in MU1, ST1.
  pose proof (rw_cells_transport rsegs _ mem m1 _ _ HS1 MU1 WM1
    ltac:(cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 338; repeat split; lia)) as HS1'.
  pose proof (rw_cells_transport rsegs _ mem m1 _ _ HR MU1 WM1
    ltac:(cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 288; repeat split; lia)) as HR1.
  pose proof (bytes_at_transport rsegs _ mem m1 _ _ HB MU1
    ltac:(cbn [disjoint_from]; rewrite Lbs; repeat split; lia)) as HB1.
  assert (MU1' : munch [(lo, spv + 360); (r, r + 288)] mem m1).
  { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros x Hx; repeat split; lia. }
  pose proof (munch_trans _ mem mem m1 MU MU1') as MU2. clear MU1'.
  pose proof (wmono_trans rsegs mem mem m1 WM WM1) as WM2.
  clear MU MU1 WM WM1 HS1 HR HB HP ST MI.
  destruct (c2_cb_bytes _ _ _ _ HM1) as [HM LM].
  lazymatch type of HS1' with
  | rw_cells _ _ _ ?cs1 =>
      lazymatch type of HM1 with
      | rw_cells _ _ _ ?cs2 =>
          lazymatch type of HC1 with
          | rw_cells _ _ _ ?cs3 =>
              pose proof (c2_mac8 _ _ _ _ _ _ _ _ _ _ _ _ _
                (c2_join3 m1 spv cs1 cs2 cs3 338 6 HS1' HM1 ltac:(replace (spv + 338 + 6) with (spv + 344) by lia;
                  exact HC1) eq_refl eq_refl)) as HSJ
          end
      end
  end.
  clear HS1' HM1 HC1.
  lazymatch type of HSJ with context [read_mac_used ?f ?nn] =>
    pose proof (c2_used f nn ltac:(lia)) as HU; set (u := read_mac_used f nn) in * end.
  lazymatch type of HM with bytes_at _ _ _ ?Mx => set (M := Mx) in * end.
  step. step. step.
  eapply evt_cut.
  { eapply FIND with (lo := lo) (r := r) (p := spv + 338) (bs := bs) (M := M);
      [ reflexivity | fnd_eq | exact HB1 | exact Lbs | exact B1 | exact HM | exact LM | lia
      | clear - Hr16; Z.div_mod_to_equations; lia | lia | rewrite Hspv; exact ST1 | rewrite Hspv; lia
      | rewrite Hspv; lia | rewrite Hspv; lia | exact MI1 ]. }
  post_call rsegs m1.
  match goal with H : exists z, _ = Z_to_bv 64 z /\ find_result _ _ z |- _ => destruct H as (z & Ez & FRz) end.
  match type of Ez with ?x = _ => subst x end.
  assert (Zb : -1 <= z < bx_n bs).
  { destruct FRz as [[_ ->] | [[_ (Hz & _ & _)] | (_ & -> & _)]]; lia. }
  match goal with H : bytes_at rsegs ?mm r bs |- _ =>
    pose proof (rd4_bytes_at _ r bs 280 H ltac:(lia) ltac:(rewrite Lbs; lia)) as BN end.
  change (rd4 bs 280) with (bx_n bs) in BN.
  pose proof (fnd_rd4 _ _ _ BN) as RN.
  step. step. step.
  if_cases HC1; [ c2_killz HC1 | ].
  step. step.
  try (change (firstn 4 (skipn 280 bs)) with (bsub bs 280 4);
       rewrite <- (le4_rd4 bs 280) by (apply bsub_length; lia); rewrite sext_extract_le4;
       change (rd4 bs 280) with (bx_n bs)).
  rewrite ?fnd_sx32 by lia.
  if_cases HC2; [ c2_killz HC2 | ].
  step.
  if_cases HC3; zify_cond HC3; rewrite ?signed_lit in HC3 by lia.
  - assert (Ez : z = -1) by lia. subst z.
    do 5 step.
    c2_zcall BC M HM.
    step. step. step.
    if_cases HC4; [ | c2_killc HC4 ].
    step. step.
    c2_end.
  - destruct FRz as [[_ E] | [[NZ (Hz & Hmac & _)] | (_ & E & _)]]; [ lia | | lia ].
    match goal with H : bytes_at rsegs ?mm r bs |- _ =>
      pose proof (bytes_at_bsub _ r bs (56 * z) 6 H ltac:(lia) ltac:(lia) ltac:(rewrite Lbs; lia)) as HBi end.
    change (bsub bs (56 * z) 6) with (bx_mac bs z) in HBi. rewrite Hmac in HBi.
    step. step.
    if_cases HU1; [ c2_killz HU1 | ].
    step. step. step. rewrite ?c2_m56 by lia.
    step.
    if_cases HU2; [ c2_killz HU2 | ].
    do 7 step.
    eapply evt_cut.
    { eapply BC with (ls := M) (rs := M) (v := 0);
        [ eapply c2_bv; [ exact HBi | apply c2_idx; lia | lia ] | eapply c2_bv; [ exact HM | fnd_eq | lia ]
        | change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat; apply c2_memcmp_eq; exact LM | assumption ]. }
    c2_post.
    step. step.
    if_cases HC5; [ c2_killc HC5 | ].
    do 5 step.
    c2_zcall BC M HM.
    step. step. step.
    if_cases HC4; [ c2_killz HC4 | ].
    step. step.
    if_cases HC6; [ | ].
    + exfalso. zify_cond HC6. rewrite ?unsigned_lit_wrap in HC6.
      match goal with Rv : -256 < ?v < 256, Iv : ?v = 0 <-> _ |- _ =>
        assert (V : v = 0) by (clear - HC6 Rv; Z.div_mod_to_equations; lia); apply Iv in V; exact (NZ V) end.
    + step. c2_end.
Qed.

Section C2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Theorem llvm_case2_ok : llvm_case_ok B API 2.
Proof.
  exact (llvm_case_of_evt B API 2
    (c2_evt (read_mac_holds memcpy_holds) (reac_boxreg_find_holds mac_is_zero_holds bcmp_holds) bcmp_holds)).
Qed.

End C2.
