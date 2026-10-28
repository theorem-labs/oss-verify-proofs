(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan AsHSTab AsMainVM. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import PerfLia.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pm_vmem (sp0z brk0z : Z) (X : pm_syms) (FULL : word -> option byte) : word -> option byte :=
  restrict_mem (zz2ww (PM_LAZY sp0z X)) (zz2ww (PM_S sp0z brk0z X)) FULL.

Lemma asegs_ASEGS : asegs = ASEGS.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma seg_rom_lib : Lib.PropExec.seg_rom = PropExec.seg_rom.
Proof. reflexivity. Qed.
Lemma rdn_lib : Lib.PropExec.rdn = PropExec.rdn.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_mrd : forall segs bs m (a : Z),
  PropExec.rdn segs m (Z_to_bv 64 a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  forall i, (i < length bs)%nat -> mrd segs m (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros segs bs. induction bs as [|b bs IH]; intros m a H Ha Hn i Hi; [cbn in Hi; lia|].
  cbn [length] in Hn. cbn [rdn length] in H.
  unfold mrd. rewrite seg_rom_lib.
  destruct i as [|i].
  - cbn [nth_error]. rewrite Z.add_0_r. unfold wa.
    destruct (match m (Z_to_bv 64 a) with Some b0 => Some b0 | None => PropExec.seg_rom segs (Z_to_bv 64 a) end) as [b'|]; [|discriminate].
    destruct (PropExec.rdn segs m (Z_to_bv 64 a + 1)%bv (length bs)); [|discriminate]. congruence.
  - cbn [nth_error]. cbn [length] in Hi.
    destruct (match m (Z_to_bv 64 a) with Some b0 => Some b0 | None => PropExec.seg_rom segs (Z_to_bv 64 a) end) as [b'|]; [|discriminate].
    destruct (PropExec.rdn segs m (Z_to_bv 64 a + 1)%bv (length bs)) as [r|] eqn:Hr; [|discriminate].
    injection H as <- <-.
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) in Hr
      by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; change (bv_unsigned (1%bv : word)) with 1;
          unfold bv_wrap; rewrite Zplus_mod_idemp_l; reflexivity).
    pose proof (IH m (a + 1) Hr ltac:(lia) ltac:(lia) i ltac:(lia)) as IH'. unfold mrd in IH'. rewrite seg_rom_lib in IH'.
    replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. exact IH'.
Qed.

(* [comment removed for export] *)
Lemma img_rw_wview : forall m (a : Z), 0x571000 <= a < 0xc04000 -> wview asegs m (wa a) <> None.
Proof. intros m a Ha. rewrite asegs_ASEGS. apply asan_rw_window. rewrite wa_unsigned by lia. exact Ha. Qed.

(* [comment removed for export] *)
Lemma img_rw_rom : forall (a : Z), 0x571000 <= a < 0xc04000 -> exists b, PropExec.seg_rom ASEGS (wa a) = Some b.
Proof.
  intros a Ha. pose proof (asan_rw_window (fun _ => None) (wa a)) as W.
  rewrite wa_unsigned in W by lia. specialize (W Ha).
  unfold wview in W. unfold PropExec.seg_rom, memory_read. rewrite wa_unsigned in W |- * by lia.
  change (Z.of_N 1) with 1.
  destruct (find_segment ASEGS a 1) as [seg|] eqn:Hf; [|exfalso; exact (W eq_refl)].
  assert (HR : seg_readable seg = true /\ seg_writable seg = true).
  { apply find_segment_some_spec in Hf as (Hin & _ & _). rewrite asan_segs_eq in Hin.
    destruct (seg_writable seg) eqn:SW; [|exfalso; exact (W eq_refl)].
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in SW |- *; split; congruence. }
  destruct HR as [-> HW]. rewrite HW in W. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))) as [b|]; [|exfalso; exact (W eq_refl)].
  exists b; reflexivity.
Qed.

Lemma mrd_img_rw : forall m (a : Z), 0x571000 <= a < 0xc04000 -> exists b, mrd asegs m (wa a) = Some b.
Proof.
  intros m a Ha. unfold mrd. rewrite seg_rom_lib, asegs_ASEGS. destruct (m (wa a)) as [b|]; [exists b; reflexivity|]. apply img_rw_rom. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma stk_img_rw : forall m lo hi, 0x571000 <= lo -> hi <= 0xc04000 -> lo <= hi -> stk asegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi Hle. split; [lia|]. split; [lia|]. intros a Ha. split; [apply img_rw_wview; lia | apply mrd_img_rw; lia].
Qed.

(* [comment removed for export] *)
Lemma stk_of_some : forall m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> exists b, m (wa a) = Some b) -> stk asegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha. destruct (H a Ha) as [b Hb].
  split; [unfold wview; rewrite Hb; discriminate | exists b; unfold mrd; rewrite Hb; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma bytes_at_of_nth : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> mrd asegs m (wa (a + Z.of_nat i)) = nth_error bs i) -> bytes_at asegs m a bs.
Proof. intros m a bs Ha Hn H. split; [lia|]. split; [lia|]. exact H. Qed.

(* [comment removed for export] *)
Lemma wr_at_of_some : forall m a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, m (wa (a + i)) = Some b) -> wr_at asegs m a n.
Proof.
  intros m a n Ha Hn H. split; [lia|]. split; [lia|]. intros i Hi. destruct (H i Hi) as [b Hb]. unfold wview. rewrite Hb. discriminate.
Qed.
Lemma wr_at_img_rw : forall m a n, 0x571000 <= a -> a + n <= 0xc04000 -> wr_at asegs m a n.
Proof. intros m a n Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. apply img_rw_wview. lia. Qed.

(* [comment removed for export] *)
Lemma pairwise_apart_nth : forall l i j p q, pairwise_apart l -> (i < j)%nat ->
  nth_error l i = Some p -> nth_error l j = Some q -> fst p + snd p <= fst q \/ fst q + snd q <= fst p.
Proof.
  induction l as [|[a n] l IH]; intros i j p q H Hij Hp Hq; [destruct i; discriminate|].
  cbn [pairwise_apart] in H. destruct H as [HF H].
  destruct i as [|i]; destruct j as [|j]; [lia| | lia |].
  - cbn in Hp. injection Hp as <-. cbn in Hq. apply nth_error_In in Hq. cbn [fst snd].
    exact (proj1 (Forall_forall _ _) HF q Hq).
  - cbn in Hp, Hq. exact (IH i j p q H ltac:(lia) Hp Hq).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia_leaf := lazymatch goal with |- _ \/ _ => fail | |- _ => lia end.
Ltac solve_disj := first [ lia_leaf | (left; solve_disj) | (right; solve_disj) ].
(* [comment removed for export] *)
Ltac zinP_norm2 := cbn [zinP fst snd app]; repeat (rewrite ?zinP_app, ?(zinP_ifr (Z_to_bv 64 0) (Z_to_bv 64 0)); cbn [zinP fst snd app]).
(* [comment removed for export] *)
Ltac zcases H := lazymatch type of H with _ \/ _ => destruct H as [H|H]; [|zcases H] | False => destruct H | _ => idtac end.

Section AT_MAIN.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : valid_sp sp0.
  Hypothesis Vbrk : valid_brk ASEGS brk0.
  Hypothesis Vav : valid_argv (in_argv inp).
  Hypothesis Vev : valid_envp (in_envp inp).
  Hypothesis Vfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp).
  Hypothesis Hh : HSF_asan h = Some ch.
  Hypothesis HC : cs_ok ASEGS ASAN_H AsanInit.LIMIT (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
                        (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model.
  #[local] Notation g := (hole_granted h).
  #[local] Notation cls := (hole_class h).
  Let X := Xof g E.
  Let brk0z := bv_unsigned brk0.
  Let sp0z := bv_unsigned sp0.
  Let argc := Z.of_nat (length (in_argv inp)).
  (* [comment removed for export] *)
  Let VM := pm_vmem sp0z brk0z X FULL.
  (* [comment removed for export] *)
  Let MC : PMC sp0 rdraw inp brk0z X FULL := PMC_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC.
  Let SOK : pm_syms_ok sp0z brk0z 0 X := pm_syms_ok_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC.

  (* [comment removed for export] *)
  Ltac prepI :=
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP);
    let B := fresh "B" in let Bg := fresh "Bg" in let B13 := fresh "B13" in
    pose proof (KB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as B; cbv zeta in B; destruct B as [B B13];
    unfold pm_kernel_placed in B; rewrite Forall_app in B; destruct B as [B Bg];
    unfold GHZ, Xof in B, Bg, B13;
    cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_b24 ps_a1 ps_a2 ps_a3 ps_g1 ps_g2 ps_g3 ps_g4 ps_granted] in B, Bg, B13;
    repeat (apply Forall_cons_iff in B as [? B]);
    (let BG4 := fresh "BG4" in let BG3 := fresh "BG3" in let BG2 := fresh "BG2" in let BG1 := fresh "BG1" in
     apply Forall_cons_iff in B13 as [BG4 B13]; apply Forall_cons_iff in B13 as [BG3 B13]; apply Forall_cons_iff in B13 as [BG2 B13];
     apply Forall_cons_iff in B13 as [BG1 B13]; apply Forall_inv in B13);
    cbn [fst snd] in *;
    pose proof (u64_range brk0) as ?Hb0; pose proof (u64_range sp0) as ?Hs0;
    pose proof (RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl REL) as ?HRIv.
  Ltac zlistsI :=
    unfold VM, pm_vmem, X, sp0z, brk0z in *;
    unfold PM_LAZY, PM_S, PM_ZR, PM_NOACC, PM_MAPS, PM_REM, VISZ, VISZ0, GHZ, SW;
    rewrite ?(RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl) by assumption;
    unfold Xof in *; cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_b24 ps_a1 ps_a2 ps_a3 ps_g1 ps_g2 ps_g3 ps_g4 ps_granted map app fst snd] in *.

  (* [comment removed for export] *)
  Lemma kp_apart : forall i j p q, (i < j)%nat ->
    nth_error (pm_kernel_placed X) i = Some p -> nth_error (pm_kernel_placed X) j = Some q ->
    fst p + snd p <= fst q \/ fst q + snd q <= fst p.
  Proof. intros i j p q Hij Hp Hq. exact (pairwise_apart_nth _ _ _ _ _ (pso_apart _ _ _ _ SOK) Hij Hp Hq). Qed.
  (* [comment removed for export] *)
  Lemma kp_apart_ne : forall i j p q, i <> j ->
    nth_error (pm_kernel_placed X) i = Some p -> nth_error (pm_kernel_placed X) j = Some q ->
    fst p + snd p <= fst q \/ fst q + snd q <= fst p.
  Proof.
    intros i j p q Hij Hp Hq. destruct (Nat.lt_ge_cases i j) as [L|L].
    - exact (kp_apart i j p q L Hp Hq).
    - pose proof (kp_apart j i q p ltac:(lia) Hq Hp). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma kp_facts : forall i p, nth_error (pm_kernel_placed X) i = Some p ->
    fst p mod 4096 = 0 /\ 4096 <= fst p /\ fst p + snd p <= page_down sp0z - 8388608
    /\ (fst p + snd p <= 65536 \/ 12599296 <= fst p) /\ (fst p + snd p <= 2147446784 \/ 17594333495296 <= fst p).
  Proof.
    intros i p Hp. pose proof (nth_error_In _ _ Hp) as Hin.
    pose proof (KB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as [B _]. cbv zeta in B. fold X in B.
    pose proof (proj1 (Forall_forall _ _) B p Hin) as [B1 B2].
    pose proof (KBAND_in sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC p Hin) as [B3 B4].
    pose proof (proj1 (Forall_forall _ _) (pso_placed _ _ _ _ SOK) p Hin) as (B0 & _). repeat split; assumption.
  Qed.
  Lemma kp_align : forall i p, nth_error (pm_kernel_placed X) i = Some p -> fst p mod 4096 = 0.
  Proof. intros i p Hp. exact (proj1 (kp_facts i p Hp)). Qed.
  (* [comment removed for export] *)
  Lemma pd_facts : page_down sp0z <= sp0z < page_down sp0z + 4096 /\ 0x7fff80000000 <= page_down sp0z <= 0x800000000000 /\ page_down sp0z mod 4096 = 0.
  Proof. prepI. unfold AsMainSyms.page_down in *. unfold sp0z. lia. Qed.
  Lemma kp_b06 : nth_error (pm_kernel_placed X) 2 = Some (ps_b06 X, 0x2000011000). Proof. reflexivity. Qed.
  Lemma kp_b08 : nth_error (pm_kernel_placed X) 3 = Some (ps_b08 X, 0x800000). Proof. reflexivity. Qed.
  Lemma kp_b22 : nth_error (pm_kernel_placed X) 11 = Some (ps_b22 X, 0x800000). Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma vm_full : forall z, 0 <= z < 2 ^ 64 -> (zinP z (PM_LAZY sp0z X) -> zinP z (PM_S sp0z brk0z X)) -> VM (wa z) = FULL (wa z).
  Proof.
    intros z Hz H. unfold VM, pm_vmem, restrict_mem, restrict_mem_by, hiddenb.
    rewrite (in_rangesb_zz sp0 brk0 _ _ (zz_ok_lazy sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)).
    rewrite (in_rangesb_zz sp0 brk0 _ _ (zz_ok_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)).
    rewrite wa_unsigned by lia. fold sp0z brk0z X.
    destruct (zin z (PM_LAZY sp0z X)) eqn:HL; [|reflexivity].
    apply zin_iff in HL. apply H in HL. apply zin_iff in HL. rewrite HL. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma vm_img : forall z, 0x10000 <= z < 0xc04000 -> VM (wa z) = FULL (wa z).
  Proof.
    intros z Hz. apply vm_full; [lia|]. intros HL. exfalso. revert HL. prepI.
    pose proof (kp_facts _ _ kp_b06) as F2. pose proof (kp_facts _ _ kp_b08) as F3. pose proof (kp_facts _ _ kp_b22) as F11. cbn [fst snd] in F2, F3, F11.
    revert F2 F3 F11. zlistsI. zinP_norm2.
    intros F2 F3 F11 HL. clear MC SOK. zcases HL; (first [clear - HL F11 Hz F3 F2 REL; tlia | tlia]).
  Qed.

  (* [comment removed for export] *)
  Lemma vm_S : forall z, 0 <= z < 2 ^ 64 -> zinP z (PM_S sp0z brk0z X) -> VM (wa z) = FULL (wa z).
  Proof. intros z Hz HS. apply vm_full; [exact Hz | intros _; exact HS]. Qed.

  (* [comment removed for export] *)
  Lemma vm_obj : forall i p z, nth_error (pm_kernel_placed X) i = Some p -> i <> 2%nat -> i <> 3%nat -> i <> 11%nat ->
    fst p <= z < fst p + snd p -> VM (wa z) = FULL (wa z).
  Proof.
    intros i p z Hp N2 N3 N11 Hz. pose proof (kp_facts i p Hp) as (_ & PB1 & PB2 & PB3 & PB4).
    pose proof (kp_apart_ne _ _ _ _ N2 Hp kp_b06) as A2. pose proof (kp_apart_ne _ _ _ _ N3 Hp kp_b08) as A3.
    pose proof (kp_apart_ne _ _ _ _ N11 Hp kp_b22) as A11. cbn [fst snd] in A2, A3, A11.
    pose proof pd_facts as PD.
    apply vm_full; [lia|]. intros HL. exfalso. revert A2 A3 A11 PB2 HL. clear Hp. prepI. zlistsI. zinP_norm2.
    intros A2 A3 A11 PB2 HL. destruct p as [a n]. cbn [fst snd] in *. clear MC SOK.
    zcases HL; (first [clear - HL A11 Hz A3 A2 REL PB4; tlia | tlia]).
  Qed.

  (* [comment removed for export] *)
  Lemma vm_ri : forall z, pm_region_info X <= z < pm_region_info X + 4096 -> VM (wa z) = FULL (wa z).
  Proof.
    intros z Hz. pose proof (kp_apart 2 3 _ _ ltac:(lia) kp_b06 kp_b08) as A3. pose proof (kp_apart 2 11 _ _ ltac:(lia) kp_b06 kp_b22) as A11.
    pose proof (kp_facts _ _ kp_b06) as (_ & _ & F2 & F3 & F4). cbn [fst snd] in A3, A11, F2, F3, F4. pose proof pd_facts as PD.
    apply vm_full; [prepI; unfold X in Hz; rewrite HRIv in Hz; lia|]. intros HL. exfalso. revert A3 A11 F2 F3 F4 Hz HL. prepI. zlistsI. zinP_norm2.
    intros A3 A11 F2 F3 F4 Hz HL. clear MC SOK. zcases HL; (first [clear - HL Hz A11 REL A3 F4; tlia | tlia]).
  Qed.

  (* [comment removed for export] *)
  Lemma vm_stack : forall z, page_down sp0z - 0x800000 <= z < 2 ^ 64 -> VM (wa z) = FULL (wa z).
  Proof.
    intros z Hz. pose proof (kp_facts _ _ kp_b06) as (_ & _ & P2 & _). pose proof (kp_facts _ _ kp_b08) as (_ & _ & P3 & _).
    pose proof (kp_facts _ _ kp_b22) as (_ & _ & P11 & _). cbn [fst snd] in P2, P3, P11. pose proof pd_facts as PD.
    apply vm_full; [lia|]. intros HL. exfalso. revert P2 P3 P11 PD Hz HL. prepI. zlistsI. zinP_norm2.
    intros P2 P3 P11 PD Hz HL. clear MC SOK. zcases HL; tlia.
  Qed.

  (* [comment removed for export] *)
  Lemma vm_brk : g = true -> forall z, brk0z <= z < brk0z + 0x2000 -> VM (wa z) = FULL (wa z).
  Proof.
    intros Hg z Hz. pose proof (pso_brk _ _ _ _ SOK Hg) as [PB PBK]. unfold ALOWSH_LO in PB.
    pose proof (proj1 (Forall_forall _ _) PBK _ (nth_error_In _ _ kp_b06)) as A2.
    pose proof (proj1 (Forall_forall _ _) PBK _ (nth_error_In _ _ kp_b08)) as A3.
    pose proof (proj1 (Forall_forall _ _) PBK _ (nth_error_In _ _ kp_b22)) as A11. cbn [fst snd] in A2, A3, A11. clear PBK.
    apply vm_full; [prepI; lia|]. intros HL. exfalso. revert PB A2 A3 A11 Hz HL. prepI. zlistsI. zinP_norm2.
    intros PB A2 A3 A11 Hz HL. clear MC SOK. zcases HL; (first [clear - HL Hz A11 A3 A2 PB H1 REL; tlia | tlia]).
  Qed.

  (* [comment removed for export] *)
  Lemma seg_rom_above : forall z, 0xc04000 <= z < 2 ^ 64 -> PropExec.seg_rom ASEGS (wa z) = None.
  Proof.
    intros z Hz. unfold PropExec.seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
    destruct (find_segment ASEGS z 1) as [seg|] eqn:Hf; [|reflexivity]. exfalso.
    apply find_segment_some_spec in Hf as (Hin & Hb & Ht). rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hb, Ht; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma seg_rom_below : forall z, 0 <= z < 0x10000 -> PropExec.seg_rom ASEGS (wa z) = None.
  Proof.
    intros z Hz. unfold PropExec.seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
    destruct (find_segment ASEGS z 1) as [seg|] eqn:Hf; [|reflexivity]. exfalso.
    apply find_segment_some_spec in Hf as (Hin & Hb & Ht). rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hb, Ht; lia.
  Qed.
  Lemma mrd_above : forall m z b, 0xc04000 <= z < 2 ^ 64 -> mrd asegs m (wa z) = Some b -> m (wa z) = Some b.
  Proof.
    intros m z b Hz H. unfold mrd in H. rewrite seg_rom_lib, asegs_ASEGS, (seg_rom_above z Hz) in H. destruct (m (wa z)); congruence.
  Qed.
  Lemma mrd_outside : forall m z b, 0 <= z < 2 ^ 64 -> (z + 1 <= 65536 \/ 12599296 <= z) -> mrd asegs m (wa z) = Some b -> m (wa z) = Some b.
  Proof.
    intros m z b Hz Ho H. unfold mrd in H. rewrite seg_rom_lib, asegs_ASEGS in H.
    destruct Ho as [Ho|Ho]; [rewrite (seg_rom_below z ltac:(lia)) in H | rewrite (seg_rom_above z ltac:(lia)) in H]; destruct (m (wa z)); congruence.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vrange (lo hi : Z) : Prop :=
    forall z, lo <= z < hi -> VM (wa z) = FULL (wa z) /\ visibleZ sp0z brk0z argc X z.

  Lemma vr_sub : forall lo hi lo' hi', vrange lo hi -> lo <= lo' -> hi' <= hi -> vrange lo' hi'.
  Proof. intros lo hi lo' hi' H H1 H2 z Hz. apply H. lia. Qed.

  Lemma vr_img : forall lo hi, 0x10000 <= lo -> hi <= 0xc04000 -> vrange lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. split; [apply vm_img; lia | left; lia]. Qed.

  Lemma vr_stack : forall lo hi, sp0z - 0x800000 <= lo -> hi <= sp0z + 8 * argc + 16 -> vrange lo hi.
  Proof.
    intros lo hi Hlo Hhi z Hz. pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
    pose proof (len_av APH sp0 rdraw _ (in_envp inp) (in_uid inp) (in_hwcap inp) Vav) as LA. pose proof pd_facts as PD. unfold sp0z, argc in *.
    split; [apply vm_stack; unfold sp0z in *; lia | right; right; left; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma G_cases : (g = true /\ pm_meta_map brk0z X = brk0z /\ brk0z + 0x3000 <= 0x7fff7000)
                  \/ (g = false /\ pm_meta_map brk0z X = ps_b19r X /\ nth_error (pm_kernel_placed X) 17 = Some (ps_b19r X, 0x2000)).
  Proof.
    pose proof (pso_brk _ _ _ _ SOK) as PB. unfold pm_meta_map, pm_kernel_placed, X, Xof, ALOWSH_LO in *. cbn [ps_granted ps_b19r] in *.
    clear MC SOK VM. destruct g; [left | right]; repeat split; auto. exact (proj1 (PB eq_refl)).
  Qed.

  Lemma zinP_of_In : forall z l p, In p l -> fst p <= z < fst p + snd p -> zinP z l.
  Proof. intros z l p Hin Hz. apply zinP_In. exists p. exact (conj Hin Hz). Qed.

  (* [comment removed for export] *)
  Lemma vr_kobj_gen : forall i p (IV : nat), nth_error (pm_kernel_placed X) i = Some p -> i <> 2%nat -> i <> 3%nat -> i <> 11%nat -> i <> 17%nat ->
    nth_error (VISK sp0z brk0z X) IV = Some p -> vrange (fst p) (fst p + snd p).
  Proof.
    intros i p IV KP N2 N3 N11 N14 HV z Hz. split; [exact (vm_obj _ _ z KP N2 N3 N11 Hz)|].
    right. left. split; [exact (zinP_of_In z _ p (nth_error_In _ _ HV) Hz)|].
    pose proof (kp_facts _ _ KP) as (_ & PB1 & PB2 & PB3 & PB4).
    pose proof (kp_apart_ne i 2 _ _ N2 KP kp_b06) as A2. pose proof (kp_apart_ne i 3 _ _ N3 KP kp_b08) as A3. cbn [fst snd] in A2, A3.
    pose proof G_cases as GC. pose proof pd_facts as PD.
    destruct GC as [(Hg & HG & PBK)|(Hg & HG & PBK)].
    - pose proof (proj1 (Forall_forall _ _) (proj2 (pso_brk _ _ _ _ SOK Hg)) _ (nth_error_In _ _ KP)) as A14. cbv beta in A14.
      revert Hz A14; unfold visibleZ; prepI; zlistsI; rewrite HG; zinP_norm2; intros Hz A14 HN; destruct p as [a n]; cbn [fst snd] in *.
      clear MC SOK. zcases HN; (first [clear - HN A14 Hz A3 REL A2 PB4; tlia | tlia]).
    - pose proof (kp_apart_ne i 17 _ _ N14 KP PBK) as A14. cbn [fst snd] in A14.
      revert Hz A14; unfold visibleZ; prepI; zlistsI; rewrite HG; zinP_norm2; intros Hz A14 HN; destruct p as [a n]; cbn [fst snd] in *.
      clear MC SOK. zcases HN; (first [clear - HN A14 Hz A3 REL A2 PB4; tlia | tlia]).
  Qed.
  Lemma kp_b04 : nth_error (pm_kernel_placed X) 0 = Some (ps_b04 X, 0x10000). Proof. reflexivity. Qed.
  Lemma kp_b05 : nth_error (pm_kernel_placed X) 1 = Some (ps_b05 X, 0x38e000). Proof. reflexivity. Qed.
  Lemma kp_b09 : nth_error (pm_kernel_placed X) 4 = Some (ps_b09 X, 0x1000). Proof. reflexivity. Qed.
  Lemma kp_b10 : nth_error (pm_kernel_placed X) 5 = Some (ps_b10 X, 0x10000). Proof. reflexivity. Qed.
  Lemma kp_b11 : nth_error (pm_kernel_placed X) 6 = Some (ps_b11 X, 0x1000). Proof. reflexivity. Qed.
  Lemma kp_b12 : nth_error (pm_kernel_placed X) 7 = Some (ps_b12 X, 0x1000). Proof. reflexivity. Qed.
  Lemma kp_b16 : nth_error (pm_kernel_placed X) 8 = Some (ps_b16 X, 0xb09000). Proof. reflexivity. Qed.
  Lemma kp_b20 : nth_error (pm_kernel_placed X) 9 = Some (ps_b20 X, 0x1000). Proof. reflexivity. Qed.
  Lemma kp_b21 : nth_error (pm_kernel_placed X) 10 = Some (ps_b21 X, 0x100000). Proof. reflexivity. Qed.
  Lemma kp_b23 : nth_error (pm_kernel_placed X) 12 = Some (ps_b23 X, 0x1000). Proof. reflexivity. Qed.
  Lemma kp_b24 : nth_error (pm_kernel_placed X) 16 = Some (ps_b24 X, 0x10000). Proof. reflexivity. Qed.
  Lemma kp_a1 : nth_error (pm_kernel_placed X) 13 = Some (ps_a1 X, 0x10000). Proof. reflexivity. Qed.
  Lemma kp_a2 : nth_error (pm_kernel_placed X) 14 = Some (ps_a2 X, 0x10000). Proof. reflexivity. Qed.
  Lemma kp_a3 : nth_error (pm_kernel_placed X) 15 = Some (ps_a3 X, 0x10000). Proof. reflexivity. Qed.
  Lemma vr_b04 : vrange (ps_b04 X) (ps_b04 X + 0x10000).    Proof. exact (vr_kobj_gen _ _ 16 kp_b04 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b05 : vrange (ps_b05 X) (ps_b05 X + 0x38e000).   Proof. exact (vr_kobj_gen _ _ 15 kp_b05 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b09 : vrange (ps_b09 X) (ps_b09 X + 0x1000).     Proof. exact (vr_kobj_gen _ _ 13 kp_b09 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b10 : vrange (ps_b10 X) (ps_b10 X + 0x10000).    Proof. exact (vr_kobj_gen _ _ 12 kp_b10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b11 : vrange (ps_b11 X) (ps_b11 X + 0x1000).     Proof. exact (vr_kobj_gen _ _ 11 kp_b11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b12 : vrange (ps_b12 X) (ps_b12 X + 0x1000).     Proof. exact (vr_kobj_gen _ _ 10 kp_b12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b16 : vrange (ps_b16 X) (ps_b16 X + 0xb09000).   Proof. exact (vr_kobj_gen _ _ 9 kp_b16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b20 : vrange (ps_b20 X) (ps_b20 X + 0x1000).     Proof. exact (vr_kobj_gen _ _ 7 kp_b20 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b21 : vrange (ps_b21 X) (ps_b21 X + 0x100000).   Proof. exact (vr_kobj_gen _ _ 6 kp_b21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b23 : vrange (ps_b23 X) (ps_b23 X + 0x1000).     Proof. exact (vr_kobj_gen _ _ 4 kp_b23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_b24 : vrange (ps_b24 X) (ps_b24 X + 0x10000).    Proof. exact (vr_kobj_gen _ _ 0 kp_b24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_a1 : vrange (ps_a1 X) (ps_a1 X + 0x10000).      Proof. exact (vr_kobj_gen _ _ 3 kp_a1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_a2 : vrange (ps_a2 X) (ps_a2 X + 0x10000).      Proof. exact (vr_kobj_gen _ _ 2 kp_a2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.
  Lemma vr_a3 : vrange (ps_a3 X) (ps_a3 X + 0x10000).      Proof. exact (vr_kobj_gen _ _ 1 kp_a3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). Qed.

  (* [comment removed for export] *)
  Lemma vm_sw : forall a n x, In (a, n) (VISZ sp0z brk0z X) -> 0 <= a -> a <= x < a + n -> a + n <= 2 ^ 47 -> (a + n) mod 8 = 0 ->
    VM (wa (SHOFF + x / 8)) = FULL (wa (SHOFF + x / 8)).
  Proof.
    intros a n x Hin Ha Hx Hhi H8. apply vm_S; [unfold SHOFF in *; lia|].
    unfold PM_S. cbn [zinP]. right. apply (zinP_of_In _ _ (SW a n)); [apply in_map_iff; exists (a, n); split; [reflexivity | exact Hin]|].
    unfold SW. cbn [fst snd]. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma vm_b22 : forall z, ps_b22 X <= z < ps_b22 X + 0x800000 -> VM (wa z) = FULL (wa z).
  Proof.
    intros z Hz. pose proof (kp_facts _ _ kp_b22) as (_ & P1 & P2 & _). cbn [fst snd] in P1, P2. pose proof pd_facts as PD.
    apply vm_S; [lia|]. unfold PM_S. cbn [zinP fst snd]. left. exact Hz.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation CXV a := (cx_val sp0z brk0z X a).
  Lemma world_ok_X : forall w, world_ok w (pm_short sp0z) g -> world_ok w (pm_short (bv_unsigned sp0)) (ps_granted X).
  Proof. intros w Hw. exact Hw. Qed.

  (* [comment removed for export] *)
  Lemma bytes_main : forall w a zs, bytes_check_w w a zs = true -> world_ok w (pm_short sp0z) g ->
    0 <= CXV a -> CXV a + Z.of_nat (length zs) <= 2 ^ 64 -> vrange (CXV a) (CXV a + Z.of_nat (length zs)) ->
    bytes_at asegs VM (CXV a) (map b8 zs).
  Proof.
    intros w a zs Hc Hw H0 H1 VR.
    pose proof (pmc_bytes_w _ _ _ _ _ _ MC w a zs Hc (world_ok_X w Hw) H0 H1 ltac:(intros i Hi; destruct (VR (CXV a + i) ltac:(lia)) as [_ Hv]; exact Hv)) as RD.
    apply bytes_at_of_nth; [lia | rewrite length_map; lia |]. intros i Hi. rewrite length_map in Hi.
    destruct (VR (CXV a + Z.of_nat i) ltac:(lia)) as [V _]. unfold mrd. rewrite V. fold (mrd asegs FULL (wa (CXV a + Z.of_nat i))).
    rewrite <- (length_map b8) in RD, Hi. rewrite asegs_ASEGS. apply (rdn_mrd ASEGS (map b8 zs) FULL (CXV a) RD ltac:(lia) ltac:(rewrite length_map; lia) i Hi).
  Qed.

  (* [comment removed for export] *)
  Lemma word_main : forall w a v, word_check_w w a v = true -> world_ok w (pm_short sp0z) g ->
    0 <= CXV a -> CXV a + 8 <= 2 ^ 64 -> vrange (CXV a) (CXV a + 8) ->
    bytes_at asegs VM (CXV a) (le8 (wz (CXV v))).
  Proof.
    intros w a v Hc Hw H0 H1 VR.
    pose proof (pmc_word_w _ _ _ _ _ _ MC w a v Hc (world_ok_X w Hw) H0 H1 ltac:(intros i Hi; destruct (VR (CXV a + i) ltac:(lia)) as [_ Hv]; exact Hv)) as RD.
    assert (HL : length (le8 (wz (CXV v))) = 8%nat) by reflexivity.
    apply bytes_at_of_nth; [lia | rewrite HL; lia |]. intros i Hi. rewrite HL in Hi.
    destruct (VR (CXV a + Z.of_nat i) ltac:(lia)) as [V _]. unfold mrd. rewrite V. fold (mrd asegs FULL (wa (CXV a + Z.of_nat i))).
    rewrite asegs_ASEGS. apply (rdn_mrd ASEGS (le8 (wz (CXV v))) FULL (CXV a)); [exact RD | lia | rewrite HL; lia | rewrite HL; exact Hi].
  Qed.

  (* [comment removed for export] *)
  Lemma zero_main : forall w a n, zero_check_w w a n = true -> world_ok w (pm_short sp0z) g -> 0 <= n < 2 ^ 64 ->
    (forall z, CXV a <= z < CXV a + n -> VM (wa z) = FULL (wa z)) ->
    forall z, CXV a <= z < CXV a + n -> VM (wa z) = Some (b8 0).
  Proof.
    intros w a n Hc Hw Hn V z Hz. rewrite (V z Hz).
    pose proof (pmc_zero_w _ _ _ _ _ _ MC w a n Hc (world_ok_X w Hw) Hn (z - CXV a) ltac:(lia)) as Z0. unfold sp0z in *.
    replace (cx_val (bv_unsigned sp0) brk0z X a + (z - cx_val (bv_unsigned sp0) brk0z X a)) with z in Z0 by lia. exact Z0.
  Qed.
  (* [comment removed for export] *)
  Lemma fill_main : forall w a n c, fill_check_w w a n c = true -> world_ok w (pm_short sp0z) g ->
    (forall z, CXV a <= z < CXV a + n -> VM (wa z) = FULL (wa z)) ->
    forall z, CXV a <= z < CXV a + n -> VM (wa z) = Some (b8 c).
  Proof.
    intros w a n c Hc Hw V z Hz. rewrite (V z Hz).
    pose proof (pmc_fill_w _ _ _ _ _ _ MC w a n c Hc (world_ok_X w Hw) (z - CXV a) ltac:(lia)) as Z0. unfold sp0z in *.
    replace (cx_val (bv_unsigned sp0) brk0z X a + (z - cx_val (bv_unsigned sp0) brk0z X a)) with z in Z0 by lia. exact Z0.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_const : forall m lo k c, 0 <= lo -> lo + Z.of_nat k <= 2 ^ 64 ->
    (forall z, lo <= z < lo + Z.of_nat k -> m (wa z) = Some (b8 c)) -> bytes_at asegs m lo (repeat (b8 c) k).
  Proof.
    intros m lo k c H0 H1 H. apply bytes_at_of_nth; rewrite ?repeat_length; [lia | lia |].
    intros i Hi. unfold mrd. rewrite (H (lo + Z.of_nat i) ltac:(lia)). symmetry. apply nth_error_repeat. exact Hi.
  Qed.
  Lemma u8arr_const : forall m lo k c, 0 <= lo -> lo + Z.of_nat k <= 2 ^ 64 ->
    (forall z, lo <= z < lo + Z.of_nat k -> m (wa z) = Some (b8 c)) -> u8arr asegs m lo (repeat (b8 c) k).
  Proof.
    intros m lo k c H0 H1 H. split; [apply bytes_at_const; assumption|].
    rewrite repeat_length. apply wr_at_of_some; [lia | lia |]. intros i Hi. exists (b8 c). apply H. lia.
  Qed.

  Lemma bytes_at_constZ : forall m lo n c, 0 <= lo -> 0 <= n -> lo + n <= 2 ^ 64 ->
    (forall z, lo <= z < lo + n -> m (wa z) = Some (b8 c)) -> bytes_at asegs m lo (repeat (b8 c) (Z.to_nat n)).
  Proof. intros m lo n c H0 H1 H2 H. apply bytes_at_const; rewrite ?Z2Nat.id by lia; [lia | lia | exact H]. Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_img : forall m A cs, cells_wf cs -> 0x571000 <= A -> A + Z.of_nat (cells_size cs) <= 0xc04000 ->
    bytes_at asegs m A (cells_bytes cs) -> rw_cells asegs m A cs.
  Proof.
    intros m A cs WF H0 H1 HB. split; [split; [exact WF | exact HB]|]. apply wr_at_img_rw; lia.
  Qed.
  Lemma rw_cells_above : forall m A cs, cells_wf cs -> 0xc04000 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
    bytes_at asegs m A (cells_bytes cs) -> rw_cells asegs m A cs.
  Proof.
    intros m A cs WF H0 H1 HB. split; [split; [exact WF | exact HB]|].
    apply wr_at_of_some; [lia | lia |]. intros i Hi. destruct HB as (_ & _ & HB).
    pose proof (cells_bytes_length cs WF) as HL.
    specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat i)) as [b|] eqn:Hn; [|apply nth_error_None in Hn; lia].
    exists b. apply (mrd_above m (A + i) b); [lia | exact HB].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac csz := cbn [cells_size csize cells_bytes cbytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map] in *.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cellsZ (cs : list cell) : list Z := map bv_unsigned (cells_bytes cs).
  Fixpoint cells_wfb (cs : list cell) : bool :=
    match cs with [] => true | CB n bs :: r => Nat.eqb (length bs) n && cells_wfb r | _ :: r => cells_wfb r end.
  Lemma cells_wfb_sound : forall cs, cells_wfb cs = true -> cells_wf cs.
  Proof.
    induction cs as [|c cs IH]; intros H; [exact I|]. cbn [cells_wfb] in H. cbn [cells_wf].
    destruct c; try (split; [exact I | exact (IH H)]). apply andb_prop in H as [H1 H2]. split; [apply Nat.eqb_eq; exact H1 | exact (IH H2)].
  Qed.
  Lemma map_b8_unsigned : forall l : list byte, map b8 (map bv_unsigned l) = l.
  Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. unfold b8. apply definitions.Z_to_bv_bv_unsigned. Qed.
  Lemma map_b8_cellsZ : forall cs, map b8 (cellsZ cs) = cells_bytes cs.
  Proof. intros cs. unfold cellsZ. apply map_b8_unsigned. Qed.
  Lemma length_cellsZ : forall cs, cells_wf cs -> length (cellsZ cs) = cells_size cs.
  Proof. intros cs WF. unfold cellsZ. rewrite length_map. apply cells_bytes_length. exact WF. Qed.
  Ltac cszl := rewrite ?length_cellsZ in * by (cbn; tauto); csz.

  (* [comment removed for export] *)
  Definition img_cells_check (A : Z) (cs : list cell) : bool :=
    cells_wfb cs && Z.leb 0x571000 A && Z.leb (A + Z.of_nat (cells_size cs)) 0xc04000 && bytes_check (CAbs, A) (cellsZ cs).
  Lemma img_cells_main : forall A cs, img_cells_check A cs = true -> rw_cells asegs VM A cs.
  Proof.
    intros A cs H. unfold img_cells_check in H. apply andb_prop in H as [H HB]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
    apply cells_wfb_sound in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
    apply rw_cells_img; [exact H0 | lia | lia |].
    pose proof (bytes_main w_all (CAbs, A) (cellsZ cs) HB (world_ok_all _ _)) as B. revert B. pmc_simpl. rewrite (length_cellsZ cs H0), Z.add_0_l. intros B.
    rewrite <- map_b8_cellsZ. apply B; [lia | lia | apply vr_img; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma lowsh_vm : forall z, SHOFF + 0x10000 / 8 <= z < SHOFF + 0xc04000 / 8 -> VM (wa z) = FULL (wa z).
  Proof.
    intros z Hz. replace z with (SHOFF + (8 * (z - SHOFF)) / 8) by (unfold SHOFF; lia).
    apply (vm_sw 0x10000 0xbf4000); [| lia | unfold SHOFF in *; lia | lia | reflexivity].
    unfold VISZ, VISZ0. apply in_or_app. left. cbn [In]. do 17 right. left. reflexivity.
  Qed.
  Lemma lowsh_vis : forall z, SHOFF + 0x10000 / 8 <= z < SHOFF + 0xc04000 / 8 -> visibleZ sp0z brk0z argc X z.
  Proof.
    intros z Hz. right. right. right. split; [exists 0x10000, 0xbf4000; split; [unfold VISZ0; cbn [In]; do 17 right; left; reflexivity | unfold SHOFF in *; lia]|].
    pose proof G_cases as GC. pose proof (kp_facts _ _ kp_b06) as (_ & _ & F2 & F3 & F4). pose proof (kp_facts _ _ kp_b08) as (_ & _ & P2 & P3 & P4). cbn [fst snd] in F2, F3, F4, P2, P3, P4.
    destruct GC as [(Hg & HG & PBK)|(Hg & HG & PBK)]; [|pose proof (kp_facts 17 _ PBK) as (_ & _ & B14 & B14a & B14b); cbn [fst snd] in B14, B14a, B14b];
      revert Hz F2 F3 F4 P2 P3 P4; prepI; zlistsI; rewrite HG; zinP_norm2; unfold SHOFF; intros Hz F2 F3 F4 P2 P3 P4; clear MC SOK VM;
      (split; [do 20 right; left; lia | intros HN; zcases HN; (first [clear - HN Hz PBK P4 F4 H1 REL B14b; lia | lia])]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma u8arr_constZ : forall m lo n c, 0 <= lo -> 0 <= n -> lo + n <= 2 ^ 64 ->
    (forall z, lo <= z < lo + n -> m (wa z) = Some (b8 c)) -> u8arr asegs m lo (repeat (b8 c) (Z.to_nat n)).
  Proof. intros m lo n c H0 H1 H2 H. apply u8arr_const; rewrite ?Z2Nat.id by lia; [lia | lia | exact H]. Qed.
  Definition fact_ivl (K : kentry) : option (Z * Z) :=
    match K with
    | KZero (SA (ELit 0) off) (ELit n) | KFill (SA (ELit 0) off) (ELit n) _ | KUnk (SA (ELit 0) off) (ELit n) =>
        if Z.leb 0 n && Z.ltb n (2 ^ 62) then Some (off, off + n) else None
    | KWord (SA (ELit 0) off) w _ => Some (off, off + Z.of_nat w)
    | _ => None
    end.
  Fixpoint ivls_of (ks : list kentry) : list (Z * Z) :=
    match ks with [] => [] | K :: r => match fact_ivl K with Some iv => iv :: ivls_of r | None => ivls_of r end end.
  Fixpoint cover_sweep (fuel : nat) (lo hi : Z) (ivs : list (Z * Z)) : bool :=
    match fuel with
    | O => Z.leb hi lo
    | S f => if Z.leb hi lo then true else
             match find (fun iv => Z.leb (fst iv) lo && Z.ltb lo (snd iv)) ivs with
             | Some iv => cover_sweep f (snd iv) hi ivs
             | None => false
             end
    end.
  Definition cover_check (lo hi : Z) : bool :=
    Z.leb 0xc04000 lo && Z.leb hi (2 ^ 63) && all_holes (fun g cls ch => cover_sweep (length (kn ch)) lo hi (ivls_of (kn ch))).

  Lemma cover_sweep_sound : forall fuel lo hi ivs, cover_sweep fuel lo hi ivs = true ->
    forall z, lo <= z < hi -> exists iv, In iv ivs /\ fst iv <= z < snd iv.
  Proof.
    induction fuel as [|f IH]; intros lo hi ivs H z Hz; cbn [cover_sweep] in H.
    - apply Z.leb_le in H. lia.
    - destruct (Z.leb_spec hi lo); [lia|].
      destruct (find (fun iv => Z.leb (fst iv) lo && Z.ltb lo (snd iv)) ivs) as [iv|] eqn:Hf; [|discriminate].
      apply find_some in Hf as [Hin Hb]. apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
      destruct (Z.lt_ge_cases z (snd iv)) as [L|L]; [exists iv; split; [exact Hin | lia]|].
      exact (IH _ _ _ H z ltac:(lia)).
  Qed.
  Lemma ivls_of_In : forall ks iv, In iv (ivls_of ks) -> exists K, In K ks /\ fact_ivl K = Some iv.
  Proof.
    induction ks as [|K ks IH]; intros iv H; [destruct H|]. cbn [ivls_of] in H.
    destruct (fact_ivl K) as [iv'|] eqn:HK.
    - destruct H as [<-|H]; [exists K; split; [left; reflexivity | exact HK]|]. destruct (IH iv H) as [K' [H1 H2]]. exists K'. split; [right; exact H1 | exact H2].
    - destruct (IH iv H) as [K' [H1 H2]]. exists K'. split; [right; exact H1 | exact H2].
  Qed.
  #[local] Notation MR := (Mr ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model FULL).
  Lemma Mr_some' : forall a b, MR a = Some b -> FULL a = Some b.
  Proof. intros a b H. unfold Mr, mrestrict in H. destruct (hid _ _ _ _ _ a); [discriminate | exact H]. Qed.
  Lemma Mr_nonnull : forall a, MR a <> None -> exists b, FULL a = Some b.
  Proof. intros a H. unfold Mr, mrestrict in H. destruct (hid _ _ _ _ _ a); [congruence|]. destruct (FULL a) as [b|]; [exists b; reflexivity | congruence]. Qed.
  Lemma uE_lit' : forall n, 0 <= n < 2 ^ 64 -> uE E (ELit n) = n.
  Proof. intros n Hn. unfold uE. cbn [edenot]. rewrite u_lit64a. apply Z.mod_small. exact Hn. Qed.
  Lemma estart_lit : forall off, estart E (SA (ELit 0) off) = off.
  Proof. intros off. unfold estart. cbn [a_base a_off]. fold (uE E (ELit 0)). rewrite uE_lit' by lia. lia. Qed.

  Lemma fact_ivl_sound : forall K lo hi z, In K (kn ch) -> fact_ivl K = Some (lo, hi) -> lo <= z < hi -> 0xc04000 <= z < 2 ^ 63 ->
    exists b, FULL (wa z) = Some b.
  Proof.
    intros K lo hi z HK HF Hz Hr. pose proof (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K HK) as KO.
    destruct K as [[[n0| | | | | | |] off] w v | [[n0| | | | | | |] off] [n| | | | | | |] | | | | | [[n0| | | | | | |] off] [n| | | | | | |] | | [[n0| | | | | | |] off] [n| | | | | | |] c | [[n0| | | | | | |] off] [n| | | | | | |]];
      cbn [fact_ivl] in HF; try discriminate HF; destruct n0; try discriminate HF.
    - (* [comment removed for export] *) injection HF as <- <-. cbn [kentry_ok] in KO. destruct KO as (Hw & FL & RD).
      assert (Ha : adenot E (SA (ELit 0) off) = wa off).
      { rewrite <- (Z_to_bv_bv_unsigned (adenot E (SA (ELit 0) off))). rewrite (flat_u E _ _ FL), estart_lit. reflexivity. }
      rewrite Ha in RD. unfold word_to_le_bytes in RD. destruct FL as (F1 & F2 & F3 & F4). rewrite estart_lit in F1, F2, F4.
      pose proof (rdn_mrd ASEGS (Z_to_le_bytes w (bv_unsigned (edenot E v))) MR off
                    ltac:(rewrite length_Z_to_le_bytes; exact RD) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia)
                    (Z.to_nat (z - off)) ltac:(rewrite length_Z_to_le_bytes; lia)) as M.
      rewrite Z2Nat.id in M by lia. replace (off + (z - off)) with z in M by lia.
      destruct (nth_error (Z_to_le_bytes w (bv_unsigned (edenot E v))) (Z.to_nat (z - off))) as [b|] eqn:Hn; [|apply nth_error_None in Hn; rewrite length_Z_to_le_bytes in Hn; lia].
      unfold mrd in M. rewrite seg_rom_lib, (seg_rom_above z ltac:(lia)) in M. destruct (MR (wa z)) as [b'|] eqn:HM; [|discriminate].
      exists b'. exact (Mr_some' _ _ HM).
    - (* [comment removed for export] *) destruct (Z.leb_spec 0 n); [|discriminate HF]. destruct (Z.ltb_spec n (2 ^ 62)); [|discriminate HF]. injection HF as <- <-.
      cbn [kentry_ok] in KO. destruct KO as [FL Z0]. unfold elenZ in Z0. fold (uE E (ELit n)) in Z0. rewrite uE_lit', estart_lit in Z0 by lia.
      exists (Z_to_bv 8 0). apply Mr_some'. unfold wa. replace z with (off + (z - off)) by lia. apply Z0. lia.
    - (* [comment removed for export] *) destruct (Z.leb_spec 0 n); [|discriminate HF]. destruct (Z.ltb_spec n (2 ^ 62)); [|discriminate HF]. injection HF as <- <-.
      cbn [kentry_ok] in KO. destruct KO as [FL Z0]. unfold elenZ in Z0. fold (uE E (ELit n)) in Z0. rewrite uE_lit', estart_lit in Z0 by lia.
      exists (Z_to_bv 8 c). apply Mr_some'. unfold wa. replace z with (off + (z - off)) by lia. apply Z0. lia.
    - (* [comment removed for export] *) destruct (Z.leb_spec 0 n); [|discriminate HF]. destruct (Z.ltb_spec n (2 ^ 62)); [|discriminate HF]. injection HF as <- <-.
      cbn [kentry_ok] in KO. destruct KO as [FL Z0]. unfold elenZ in Z0. fold (uE E (ELit n)) in Z0. rewrite uE_lit', estart_lit in Z0 by lia.
      apply Mr_nonnull. unfold wa. replace z with (off + (z - off)) by lia. apply Z0. lia.
  Qed.

  Lemma cover_main : forall lo hi, cover_check lo hi = true -> forall z, lo <= z < hi -> exists b, FULL (wa z) = Some b.
  Proof.
    intros lo hi H z Hz. unfold cover_check in H. apply andb_prop in H as [H HA]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (all_holes_here sp0 brk0 h ch Hh _ HA) as HS. cbn beta in HS.
    destruct (cover_sweep_sound _ _ _ _ HS z Hz) as [iv [Hin Hiv]]. destruct (ivls_of_In _ _ Hin) as [K [HK HF]]. destruct iv as [a b].
    exact (fact_ivl_sound K a b z HK HF Hiv ltac:(lia)).
  Qed.

  Lemma lowsh_stk : stk asegs VM (sh AIMG_LO) (sh AIMG_TOP).
  Proof.
    unfold sh, AIMG_LO, AIMG_TOP. rewrite ASHADOW_BASE_val.
    apply stk_of_some; [lia | lia |]. intros a Ha. rewrite (lowsh_vm a ltac:(unfold SHOFF; lia)).
    exact (cover_main (0x7fff8000 + 0x10000 / 8) (0x7fff8000 + 0xc04000 / 8) ltac:(vm_compute; reflexivity) a Ha).
  Qed.

  (* [comment removed for export] *)
  Lemma img_word_main : forall A v, word_check (CAbs, A) v = true -> 0x571000 <= A -> A + 8 <= 0xc04000 -> rw_cells asegs VM A [C8 (wz (CXV v))].
  Proof.
    intros A v Hc H0 H1. apply rw_cells_img; [cbn; tauto | lia | csz; lia |].
    pose proof (word_main w_all (CAbs, A) v Hc (world_ok_all _ _)) as W. revert W. pmc_simpl. rewrite Z.add_0_l. intros W.
    apply W; [lia | lia | apply vr_img; lia].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition zscanN := AsanHexScan.zscanN.
  Lemma zscanN_sound : forall s fuel base n, zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (b8 0).
  Proof. exact AsanHexScan.zscanN_sound. Qed.
  Lemma segment_byte_at_zero1 : forall s (base n : N) (off : N),
    zscanN s 64 base n = true -> (base + n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N -> (base <= off < base + n)%N ->
    segment_byte_at [s] off = Some (b8 0).
  Proof.
    intros s base n off Hs Hn Hoff. cbn [segment_byte_at].
    replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true by (symmetry; apply N.ltb_lt; lia).
    replace off with (base + (off - base))%N by lia. apply (zscanN_sound s 64 base n Hs). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma obj_word_main : forall a v lo hi, word_check a v = true -> vrange lo hi -> lo <= CXV a -> CXV a + 8 <= hi -> 0xc04000 <= lo -> hi <= 2 ^ 64 ->
    rw_cells asegs VM (CXV a) [C8 (wz (CXV v))].
  Proof.
    intros a v lo hi Hc VR H0 H1 H2 H3. apply rw_cells_above; [cbn; tauto | lia | csz; lia |].
    exact (word_main w_all a v Hc (world_ok_all _ _) ltac:(lia) ltac:(lia) (vr_sub _ _ _ _ VR H0 H1)).
  Qed.
  Lemma obj_bytes_main : forall a cs lo hi, bytes_check a (cellsZ cs) = true -> cells_wfb cs = true -> vrange lo hi ->
    lo <= CXV a -> CXV a + Z.of_nat (cells_size cs) <= hi -> 0xc04000 <= lo -> hi <= 2 ^ 64 -> rw_cells asegs VM (CXV a) cs.
  Proof.
    intros a cs lo hi Hc WF VR H0 H1 H2 H3. apply cells_wfb_sound in WF. apply rw_cells_above; [exact WF | lia | lia |].
    rewrite <- map_b8_cellsZ. apply (bytes_main w_all a (cellsZ cs) Hc (world_ok_all _ _)); rewrite ?(length_cellsZ cs WF); [lia | lia |].
    eapply vr_sub; [exact VR | lia | lia].
  Qed.
  Lemma obj_zero_main : forall a n lo hi, zero_check a n = true -> (forall z, lo <= z < hi -> VM (wa z) = FULL (wa z)) ->
    lo <= CXV a -> CXV a + n <= hi -> 0 <= n < 2 ^ 64 -> forall z, CXV a <= z < CXV a + n -> VM (wa z) = Some (b8 0).
  Proof.
    intros a n lo hi Hc V H0 H1 Hn z Hz. apply (zero_main w_all a n Hc (world_ok_all _ _) Hn); [|exact Hz]. intros y Hy. apply V. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma world_uw : forall u, pm_short sp0z = u -> world_ok (WS (Some u) None) (pm_short sp0z) g.
  Proof. intros u U. split; [cbn [w_uw osel]; rewrite U; destruct u; reflexivity | reflexivity]. Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_cons1 : forall m A c cs, rw_cells asegs m A [c] -> rw_cells asegs m (A + Z.of_nat (csize c)) cs -> rw_cells asegs m A (c :: cs).
  Proof. intros m A c cs H1 H2. apply (proj2 (rw_cells_app asegs m A [c] cs)). cbn [cells_size Nat.add]. rewrite Nat.add_0_r. exact (conj H1 H2). Qed.
End AT_MAIN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem P_main_open : forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config),
  P_main sp0 brk0 mbase rdraw inp c ->
  exists (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
         (Vsp : valid_sp sp0) (Vbrk : valid_brk ASEGS brk0) (Vav : valid_argv (in_argv inp)) (Vev : valid_envp (in_envp inp))
         (Vfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp)) (Hh : HSF_asan h = Some ch)
         (HC : cs_ok ASEGS ASAN_H AsanInit.LIMIT (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
                     (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model),
    c = cfg_of ASEGS R A_MAIN FULL model
    /\ ms_mem (cfg_ms c) = FULL
    /\ PM sp0 brk0 inp (Xof (hole_granted h) E) c
    /\ pm_syms_ok (bv_unsigned sp0) (bv_unsigned brk0) 0 (Xof (hole_granted h) E)
    /\ lzok ASEGS (zz2ww (PM_LAZY (bv_unsigned sp0) (Xof (hole_granted h) E))) (zz2ww (PM_S (bv_unsigned sp0) (bv_unsigned brk0) (Xof (hole_granted h) E)))
            (zz2ww (PM_ZR (bv_unsigned sp0) (Xof (hole_granted h) E))) c
    /\ pages_total (zz2ww (PM_S (bv_unsigned sp0) (bv_unsigned brk0) (Xof (hole_granted h) E))) <= PM_S_PAGES
    /\ PMC sp0 rdraw inp (bv_unsigned brk0) (Xof (hole_granted h) E) FULL
    /\ ms_mem (restrict (zz2ww (PM_LAZY (bv_unsigned sp0) (Xof (hole_granted h) E))) (zz2ww (PM_S (bv_unsigned sp0) (bv_unsigned brk0) (Xof (hole_granted h) E))) (cfg_ms c))
       = pm_vmem (bv_unsigned sp0) (bv_unsigned brk0) (Xof (hole_granted h) E) FULL.
Proof.
  intros sp0 brk0 mbase rdraw inp c P.
  pose proof (P_main_H _ _ _ _ _ _ P) as P'. destruct P' as [(Vsp & Vbrk & Vmb & Vav & Vev & Vfit & Vuid & Vhw) (h & ch & E & R & FULL & model & Hh & _ & Hc & HC)].
  exists h, ch, E, R, FULL, model, Vsp, Vbrk, Vav, Vev, Vfit, Hh, HC.
  split; [exact Hc|]. split; [rewrite Hc; reflexivity|].
  split; [rewrite Hc; exact (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)|].
  split; [exact (pm_syms_ok_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)|].
  pose proof (lzok_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as [L1 L2].
  split; [rewrite Hc; exact L1|]. split; [exact L2|].
  split; [exact (PMC_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC)|].
  rewrite Hc. reflexivity.
Qed.

