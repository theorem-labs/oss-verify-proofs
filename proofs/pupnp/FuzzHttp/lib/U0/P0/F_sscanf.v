(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import CellConv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt ScanIntProps.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_memchr Printf_lib F_errno_location ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_rfile F_intscan_lib F_intscan_J F_vfscanf_lib F_vfscanf_pure F_vfscanf_E.

Definition hidden2 (P : Prop) := P.
Ltac stash2 H := lazymatch type of H with hidden2 _ => idtac | ?T => change T with (hidden2 T) in H end.
Ltac lia1h := first [ lia | match goal with H : hidden2 _ |- _ => unfold hidden2 in H; lia end ].
Ltac lia1f := first [ lia1h | unfold hidden2 in *; lia ].
Ltac djsolve := first [ exact I | lia1h | split; [lia1h | djsolve] ].
Local Ltac slia ::= djsolve.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition SSCANF : Z := 0x1b1d0.
Definition VSSCANF : Z := 0x1feb4.
Definition FA_VERSION : Z := 0x10365.
Definition FA_STATUS : Z := 0x105b3.
Definition SSCANF_DEPTH : Z := 1096.

Definition sscanf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T : Z) (txt : list Z) (P1 P2 P3 : Z) (w3n : nat) (lo : Z) (canary : word) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ev v1 v2 : word) (v3 : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (ERRNOA, ERRNOA + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' T (zbytes txt) /\ ssp_cells m' canary /\ rw_cells rsegs m' ERRNOA [C4 ev]
    /\ rw_cells rsegs m' P1 [C4 v1] /\ rw_cells rsegs m' P2 [C4 v2] /\ rw_cells rsegs m' P3 [CB w3n v3].

Lemma rw_cells_reshape : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Hb' Hs'. split; [split; [exact Hwf'|]|].
  - rewrite Hb'. exact Hb.
  - rewrite Hs'. exact Hw.
Qed.

Lemma file_cells_zero : forall segs m A, rw_cells segs m A [CB 232 (repeat (Z_to_bv 8 0) 232)] ->
  rw_cells segs m A [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros segs m A H. apply (rw_cells_reshape segs m A _ _ H); [cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.

Lemma stk_hi_wmono : forall (m m' : word -> option byte) lo hi, stk rsegs m lo hi -> wmono rsegs m m' -> (0x5d000 <= lo)%Z -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) WM Hlo. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw _]. pose proof (WM _ Hw) as Hw'. split; [exact Hw'|].
  unfold wview in Hw'. unfold mrd. destruct (m' (wa a)) as [b|]; [exists b; reflexivity|].
  rewrite p0_find_segment_none in Hw'; [congruence| lia | rewrite wa_unsigned by lia; lia].
Qed.

Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Lemma sscanf_gen : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (T FA : Z) (txt pre post fmtl : list Z) (ds' : list sdir) (W3num : Z) (w3n : nat) (ap3w : word)
    (P1 P2 P3 : Z) (v1 v2 : word) (v3 : list byte) (lo : Z) (canary ev : word) (r : Z),
  rtext T txt pre post -> bytes_at rsegs m T (zbytes txt) ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  (lo + 1088 <= bv_unsigned sp)%Z -> (0x5d000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z -> bv_unsigned tp = 0x3b820%Z ->
  (4096 <= T)%Z -> (T + zlength txt <= 0x2a000 \/ 0x5d000 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (T + zlength txt <= lo \/ bv_unsigned sp <= T)%Z ->
  (0x5d000 <= P1 /\ P1 + 4 <= 2^63)%Z -> (0x5d000 <= P2 /\ P2 + 4 <= 2^63)%Z -> (0x5d000 <= P3 /\ P3 + 4 <= 2^63)%Z ->
  (P1 + 4 <= lo \/ bv_unsigned sp <= P1)%Z -> (P2 + 4 <= lo \/ bv_unsigned sp <= P2)%Z ->
  (P3 + 4 <= lo \/ bv_unsigned sp <= P3 \/ (P3 = bv_unsigned sp - 8 /\ w3n = 0%nat))%Z -> (W3num = 3%Z -> P3 + 4 <= lo \/ bv_unsigned sp <= P3)%Z ->
  (P1 + 4 <= T \/ T + zlength txt <= P1)%Z -> (P2 + 4 <= T \/ T + zlength txt <= P2)%Z -> (P3 + 4 <= T \/ T + zlength txt <= P3)%Z ->
  (P1 + 4 <= P2 \/ P2 + 4 <= P1)%Z -> (P1 + 4 <= P3 \/ P3 + 4 <= P1)%Z -> (P2 + 4 <= P3 \/ P3 + 4 <= P2)%Z ->
  ssp_cells m canary -> rw_cells rsegs m ERRNOA [C4 ev] ->
  rw_cells rsegs m P1 [C4 v1] -> rw_cells rsegs m P2 [C4 v2] -> rw_cells rsegs m P3 [CB w3n v3] ->
  bytes_at rsegs m FA (zbytes fmtl) -> (0x10000 <= FA /\ FA + zlength fmtl <= 0x12000)%Z -> Forall (fun c => 0 <= c < 256)%Z fmtl ->
  fmt_enc fmtl (SD :: ds') -> (nconv (SD :: ds') <= W3num)%Z ->
  ((W3num = 2%Z /\ w3n = 0%nat) \/ (W3num = 3%Z /\ w3n = 4%nat)) -> (W3num = 3%Z -> ap3w = Z_to_bv 64 P3) ->
  sscanf_model (SD :: ds') txt (zlength pre) = Some r ->
  evt rsegs (sscanf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T txt P1 P2 P3 w3n lo canary r m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) (Z_to_bv 64 FA) (Z_to_bv 64 P1) (Z_to_bv 64 P2) ap3w a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SSCANF) fc None m (seg_rom rsegs)).
Proof.
  intros until r. intros TXT BY ST MI LO GT SPH TPV T0 TW T1 HT HP1 HP2 HP3 HP1q HP2q HP3q HP3q3 HP1t HP2t HP3t HP12 HP13 HP23 [SSP1 SSP2] ERR PC1 PC2 PC3 FMB HFA FMR FE HNC HW3 HAP3 HV.
  pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L40).
  assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (rewrite Htxt; unfold zlength; rewrite length_app; cbn; lia).
  pose proof (zbytes_length txt) as LTX. pose proof (zbytes_length fmtl) as LTF. unfold zlength in *.
  unfold got_ssp, ssp_guard in SSP1, SSP2. unfold ERRNOA in ERR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (243580, 243580 + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ PC3) as BP3. cbn [cells_size csize Nat.add] in BP3.
  assert (Hw3n : (w3n <= 4)%nat) by lia.
  stash HP1t. stash HP2t. stash HP3t. stash HP12. stash HP13. stash HP23. stash HW3.
  stash2 HT. stash2 TW. stash2 HP1q. stash2 HP2q. stash2 HP3q. stash2 HP3q3.
  pose_word_ranges.
  unfold SSCANF.

  zs. carve_frame 80%nat ST. rename FR into FRS.
  do 16 zs.

  zs. carve_frame 48%nat ST. rename FR into FRV.
  carve_frame 232%nat ST. rename FR into FILE.
  destruct (stk_split _ _ _ (bv_unsigned sp + -368)%Z _ ST ltac:(lia)) as [ST8 STJ]. clear ST. rename ST8 into ST.
  do 8 zs.
  zs. zs. zs. zs.
  zs. zs. zs. zs. callx (eapply memset_callZ; [exact FILE | assumption | lia | lia | lia | lia]).
  match goal with H : rw_cells _ _ _ [CB (Z.to_nat 232) _] |- _ =>
    change (Z.to_nat 232) with 232%nat in H; change (0 mod 256)%Z with 0%Z in H;
    apply file_cells_zero in H; rename H into FC end.

  zs. zs. zs. zs. zs. zs. zs.
  replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 M64) in FC by (apply Z_to_bv_eqm; reflexivity).
  change (repeat (Z_to_bv 8 0) 4) with zero4 in FC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FCv : rw_cells rsegs mm (bv_unsigned sp + -368 + 8) (ss_cells T 0 0 w0 T 0 w0 w0))
      by (unfold ss_cells, w0; unfold STRING_READ; replace (bv_unsigned sp + -368 + 8)%Z with (bv_unsigned sp + -360)%Z by lia; exact FC);
    pose proof (proj2 (proj1 (rw_cells_app rsegs mm _ [_; _; _; _] _) FRS)) as FRS2; cbn [cells_size csize Nat.add app] in FRS2;
    pose proof (proj1 (proj1 (rw_cells_app rsegs mm _ [_; _; _] _) FRS2)) as APC; clear FRS2;
    replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -368 + 320)%Z in APC by lia;
    apply (proj1 (rw_cells_app rsegs mm _ [_; _; _; _] _)) in FRS; destruct FRS as [FRS FRShi]; cbn [cells_size csize Nat.add app] in FRShi;
    apply (proj1 (rw_cells_app rsegs mm _ [_; _; _] _)) in FRShi; destruct FRShi as [_ FRShi]; cbn [cells_size csize Nat.add app] in FRShi;
    apply stk_of_rw_cells in FRShi; cbn [cells_size csize Nat.add] in FRShi;
    replace (bv_unsigned sp + -80 + Z.of_nat 32 + Z.of_nat 24)%Z with (bv_unsigned sp + -24)%Z in FRShi by lia;
    replace (bv_unsigned sp + -24 + Z.of_nat 24)%Z with (bv_unsigned sp) in FRShi by lia; stash FRShi end.
  clear FC.

  zs. zs. zs.
  match goal with H : stk _ ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 720)%Z _ H ltac:(lia)) as [STlo SThi]; clear H end.
  match goal with H : stk _ ?mm (bv_unsigned sp + -368)%Z _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => stash H; rename H into STJ end.
  zs.
  let v := getreg 10%Z in replace v with (Z_to_bv 64 (bv_unsigned sp + -368 + 8)) by (f_equal; lia).
  let v := getreg 12%Z in replace v with (Z_to_bv 64 (bv_unsigned sp + -368 + 320)) by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (F_vfscanf_E.L_VA (Z_to_bv 64 0x1ff24) (bv_unsigned sp + -368)%Z gp tp (Z_to_bv 64 (bv_unsigned sp + -368 + 320)) (Z_to_bv 64 FA) (Z_to_bv 64 T) (Z_to_bv 64 375432) s4 s5 s6 s7 s8 s9 s10 s11 F fc mm
                 T (Z.of_nat (length pre)) txt pre post canary P1 P2 P3 FA fmtl (S (length txt)) W3num w3n ap3w
                 TXT eq_refl eq_refl T0 ltac:(unfold zlength; lia1f) T1 ltac:(unfold VF_DEPTH; lia1f) ltac:(lia) TPV ltac:(unfold VF_DEPTH, zlength; lia1f) HP1 HP2 HP3
                 ltac:(unfold VF_DEPTH; lia1f) ltac:(unfold VF_DEPTH; lia1f) ltac:(unfold VF_DEPTH; lia1f) HP1t HP2t HP3t HP12 HP13 HP23
                 ltac:(unfold zlength; lia1f) FMR HW3 HAP3 ltac:(intros W3; specialize (HP3q3 W3); unfold VF_DEPTH; lia1f) ds') as LV end.
  cbv zeta in LV. unfold vf_post, vf_FP, VF_DEPTH, ERRNOA, VFSCANF in LV.
  eapply evt_cut; [eapply LV;
    [ replace (bv_unsigned sp + -368 - 720)%Z with (bv_unsigned sp + -368 - 720)%Z by lia; exact SThi
    | assumption | exact FCv | exact APC | exact PC1 | exact PC2 | exact PC3 | exact BY | split; [exact SSP1 | exact SSP2] | exact ERR | exact FMB | exact FE | exact HNC | exact HV ] | ].
  clear LV. intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & fjunk & ev2 & w1 & w2 & w3
                  & E & MUc & WMc & MI2 & ST2 & FCj & BY2 & [SSP3 SSP4] & ERR2 & APC2 & PCa & PCb & PCc).
  subst ms'. unfold got_ssp, ssp_guard in SSP3, SSP4.
  lazymatch type of MUc with munch ?W ?m1 _ =>
    match goal with H : rw_cells _ m1 (bv_unsigned sp + -80)%Z ?cs |- _ =>
      apply (rw_cells_transport rsegs W m1 m2 _ cs) in H; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; clear - LO GT HP1q HP2q HP3q; unfold hidden2 in *; lia]; rename H into FRS' end end.
  lazymatch type of MUc with munch ?W ?m1 _ =>
    match goal with H : rw_cells _ m1 (bv_unsigned sp + -128)%Z ?cs |- _ =>
      apply (rw_cells_transport rsegs W m1 m2 _ cs) in H; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; clear - LO GT HP1q HP2q HP3q; unfold hidden2 in *; lia]; rename H into FRV' end end.
  lazymatch type of MUc with munch ?W ?m1 _ =>
    match goal with H : stk _ m1 lo ?hi |- _ =>
      pose proof H as STc; apply (stk_transport_disjoint rsegs W m1 m2 lo hi) in H; [| exact MUc | exact WMc | cbn [disjoint_from]; clear - LO GT HP1q HP2q HP3q STc; destruct STc as (? & ? & _); unfold hidden2 in *; lia]; clear STc; rename H into STlo' end end.
  lazymatch type of MUc with munch ?W ?m1 _ =>
    match goal with H : hidden (stk _ m1 (bv_unsigned sp + -368)%Z _) |- _ =>
      unfold hidden in H; apply (stk_hi_wmono m1 m2) in H; [| exact WMc | lia]; rename H into STJ' end;
    match goal with H : hidden (stk _ m1 (bv_unsigned sp + -24)%Z _) |- _ =>
      unfold hidden in H; apply (stk_hi_wmono m1 m2) in H; [| exact WMc | lia]; rename H into FRShi' end end.
  lazymatch type of MUc with munch ?W ?m1 _ => lazymatch type of MU with munch ?Wq _ _ =>
    apply (munch_trans Wq m m1 m2) in MU end end.
  2:{ lazymatch type of MUc with munch ?W ?m1 _ => lazymatch goal with |- munch ?Wq _ _ =>
      eapply (munch_weaken W Wq m1 m2) end end.
      2: exact MUc.
      unfold sub_fp; cbn [outside]; intros xq OO. destruct OO as (O1 & O2 & O3 & O4 & O5 & OR).
      clear - O1 O2 O3 O4 O5 LO; repeat split; try assumption; first [exact I | lia | match goal with |- ?g => idtac "REM"; idtac g end]. }
  lazymatch type of MUc with munch ?W ?m1 _ =>
    match goal with H : wmono _ m m1 |- _ => apply (wmono_trans rsegs m m1 m2) in H; [| exact WMc] end;
    try clear MUc WMc; try match goal with H : mem_inv _ m1 |- _ => clear H end
  end.
  repeat match goal with H : rw_cells _ ?m1 _ _ |- _ => lazymatch m1 with m2 => fail | _ => clear H end
                  | H : bytes_at _ ?m1 _ _ |- _ => lazymatch m1 with m2 => fail | _ => clear H end end.
  replace (ret_pc (Z_to_bv 64 0x1ff24)) with (Z_to_bv 64 0x1ff24) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

  zs. zs. zs. br K1.
  zs. zs. zs. zs. zs. zs. zs.

  zs. zs. zs. br K2.
  zs. zs. zs. zs.

  pose proof (stk_merge _ _ _ _ _ STlo' ST2 ltac:(lia)) as ST5. clear STlo' ST2.
  pose proof (stk_merge _ _ _ _ _ ST5 STJ' ltac:(lia)) as ST6. clear ST5 STJ'.
  replace (bv_unsigned sp + -368 + 8)%Z with (bv_unsigned sp + -360)%Z in FCj by lia.
  release_frame FCj ST6 (bv_unsigned sp + -128)%Z.
  release_frame FRV' ST6 (bv_unsigned sp + -80)%Z.
  release_frame FRS' ST6 (bv_unsigned sp + -48)%Z.
  replace (bv_unsigned sp + -368 + 320)%Z with (bv_unsigned sp + -48)%Z in APC2 by lia.
  release_frame APC2 ST6 (bv_unsigned sp + -24)%Z.
  pose proof (stk_merge _ _ _ _ _ ST6 FRShi' ltac:(lia)) as ST7. clear ST6 FRShi'.
  match goal with H : mem_inv _ m2 |- _ => rename H into MI9 end.
  apply evt_done. unfold sscanf_post, ERRNOA.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI9|]. split; [exact ST7|].
  split; [exact BY2|]. split; [split; [exact SSP3 | exact SSP4]|]. split; [exact ERR2|].
  split; [exact PCa|]. split; [exact PCb|]. exact PCc.
Qed.

Lemma fmt_version_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m FA_VERSION (zbytes FMTL_VERSION).
Proof.
  intros m MI. assert (RO : ro_cells rsegs m FA_VERSION [CB 8 (zbytes FMTL_VERSION)]).
  { apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold FA_VERSION; lia | cbn; unfold FA_VERSION; lia]. }
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma fmt_status_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m FA_STATUS (zbytes FMTL_STATUS).
Proof.
  intros m MI. assert (RO : ro_cells rsegs m FA_STATUS [CB 11 (zbytes FMTL_STATUS)]).
  { apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold FA_STATUS; lia | cbn; unfold FA_STATUS; lia]. }
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition sscanf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T : Z) (txt pre : list Z) (P1 P2 P3 : Z) (lo : Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ev v1 v2 v3 : word) (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ sscanf_model FMT_STATUSLINE txt (zlength pre) = Some r /\ (r = -1 \/ 0 <= r <= 3)%Z
    /\ munch [(lo, bv_unsigned sp); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (ERRNOA, ERRNOA + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' T (zbytes txt) /\ ssp_cells m' canary /\ rw_cells rsegs m' ERRNOA [C4 ev]
    /\ rw_cells rsegs m' P1 [C4 v1] /\ rw_cells rsegs m' P2 [C4 v2] /\ rw_cells rsegs m' P3 [C4 v3].

Definition sscanf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (T : Z) (txt pre : list Z) (P1 P2 : Z) (lo : Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ev v1 v2 : word) (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ sscanf_model FMT_VERSION txt (zlength pre) = Some r /\ (r = -1 \/ 0 <= r <= 2)%Z
    /\ munch [(lo, bv_unsigned sp); (P1, P1 + 4); (P2, P2 + 4); (ERRNOA, ERRNOA + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' T (zbytes txt) /\ ssp_cells m' canary /\ rw_cells rsegs m' ERRNOA [C4 ev]
    /\ rw_cells rsegs m' P1 [C4 v1] /\ rw_cells rsegs m' P2 [C4 v2].

Definition sscanf_status_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (T : Z) (txt pre post : list Z) (P1 P2 P3 : Z) (v1 v2 v3 : word) (lo : Z) (canary ev : word),
  rtext T txt pre post -> bytes_at rsegs m T (zbytes txt) ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  (lo + SSCANF_DEPTH <= bv_unsigned sp)%Z -> (0x5d000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z -> bv_unsigned tp = 0x3b820%Z ->
  (4096 <= T)%Z -> (T + zlength txt <= 0x2a000 \/ 0x5d000 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (T + zlength txt <= lo \/ bv_unsigned sp <= T)%Z ->
  (0x5d000 <= P1 /\ P1 + 4 <= 2^63)%Z -> (0x5d000 <= P2 /\ P2 + 4 <= 2^63)%Z -> (0x5d000 <= P3 /\ P3 + 4 <= 2^63)%Z ->
  (P1 + 4 <= lo \/ bv_unsigned sp <= P1)%Z -> (P2 + 4 <= lo \/ bv_unsigned sp <= P2)%Z -> (P3 + 4 <= lo \/ bv_unsigned sp <= P3)%Z ->
  (P1 + 4 <= T \/ T + zlength txt <= P1)%Z -> (P2 + 4 <= T \/ T + zlength txt <= P2)%Z -> (P3 + 4 <= T \/ T + zlength txt <= P3)%Z ->
  (P1 + 4 <= P2 \/ P2 + 4 <= P1)%Z -> (P1 + 4 <= P3 \/ P3 + 4 <= P1)%Z -> (P2 + 4 <= P3 \/ P3 + 4 <= P2)%Z ->
  ssp_cells m canary -> rw_cells rsegs m ERRNOA [C4 ev] ->
  rw_cells rsegs m P1 [C4 v1] -> rw_cells rsegs m P2 [C4 v2] -> rw_cells rsegs m P3 [C4 v3] ->
  evt rsegs (sscanf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T txt pre P1 P2 P3 lo canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) (Z_to_bv 64 FA_STATUS) (Z_to_bv 64 P1) (Z_to_bv 64 P2) (Z_to_bv 64 P3) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SSCANF) fc None m (seg_rom rsegs)).

Definition sscanf_version_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (T : Z) (txt pre post : list Z) (P1 P2 : Z) (v1 v2 : word) (lo : Z) (canary ev : word),
  rtext T txt pre post -> bytes_at rsegs m T (zbytes txt) ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  (lo + SSCANF_DEPTH <= bv_unsigned sp)%Z -> (0x5d000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z -> bv_unsigned tp = 0x3b820%Z ->
  (4096 <= T)%Z -> (T + zlength txt <= 0x2a000 \/ 0x5d000 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (T + zlength txt <= lo \/ bv_unsigned sp <= T)%Z ->
  (0x5d000 <= P1 /\ P1 + 4 <= 2^63)%Z -> (0x5d000 <= P2 /\ P2 + 4 <= 2^63)%Z ->
  (P1 + 4 <= lo \/ bv_unsigned sp <= P1)%Z -> (P2 + 4 <= lo \/ bv_unsigned sp <= P2)%Z ->
  (P1 + 4 <= T \/ T + zlength txt <= P1)%Z -> (P2 + 4 <= T \/ T + zlength txt <= P2)%Z ->
  (P1 + 4 <= P2 \/ P2 + 4 <= P1)%Z ->
  ssp_cells m canary -> rw_cells rsegs m ERRNOA [C4 ev] ->
  rw_cells rsegs m P1 [C4 v1] -> rw_cells rsegs m P2 [C4 v2] ->
  evt rsegs (sscanf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T txt pre P1 P2 lo canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) (Z_to_bv 64 FA_VERSION) (Z_to_bv 64 P1) (Z_to_bv 64 P2) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SSCANF) fc None m (seg_rom rsegs)).

Theorem sscanf_status_spec : sscanf_status_stmt.
Proof.
  unfold sscanf_status_stmt. intros until ev. intros TXT BY ST MI LO GT SPH TPV T0 TW T1 HT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 SSP ERR PC1 PC2 PC3.
  pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L40).
  assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (rewrite Htxt; unfold zlength; rewrite length_app; cbn; lia).
  assert (Hnul : znth txt (zlength pre) = 0%Z) by (rewrite Htxt; rewrite znth_app_r by (unfold zlength; lia); rewrite Z.sub_diag; reflexivity).
  assert (Hpre : forall i, (0 <= i < zlength pre)%Z -> znth txt i <> 0%Z).
  { intros i Hi. rewrite Htxt. rewrite znth_app_l by exact Hi. pose proof (proj1 (Forall_forall _ _) NZ (znth pre i) (znth_In pre i Hi)). cbv beta in H. lia. }
  destruct (sscanf_model_total txt (zlength pre) Hp Hnul Hpre BYT FMT_STATUSLINE) as (r & HV & HR).
  destruct (rw_cells_forget _ _ _ _ PC3) as [b3 PC3']. cbn [cells_size csize Nat.add] in PC3'.
  unfold SSCANF_DEPTH in LO.
  eapply evt_mono.
  { eapply (sscanf_gen ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P3) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             T FA_STATUS txt pre post FMTL_STATUS [SW; SL 46; SW; SD; SW; SD] 3%Z 4%nat (Z_to_bv 64 P3) P1 P2 P3 v1 v2 b3 lo canary ev r);
      try eassumption; try LiaTuning.alia.
    - apply fmt_status_bytes. exact MI.
    - unfold FA_STATUS, FMTL_STATUS, zlength. cbn. lia.
    - unfold FMTL_STATUS. repeat constructor; lia.
    - exact fmt_enc_status.
    - cbn. lia.
    - intros _. reflexivity. }
  intros ms' PO. cbv beta in PO. unfold sscanf_post in PO. unfold sscanf3_post.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & ev' & w1 & w2 & w3 & E & REST).
  destruct REST as (MU & WM & MI' & ST' & BY' & SSP' & ERR' & PCa & PCb & PCc).
  pose proof PCc as PCc'. destruct PCc' as [[WF _] _]. cbn in WF. destruct WF as [L3 _].
  apply (rw_cells_CB_C4 rsegs m' P3 [] w3 []) in PCc. cbn [app] in PCc.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [exact E|]. split; [exact HV|]. split; [cbn in HR; lia|].
  repeat (split; [eassumption|]). exact PCc.
Qed.

Theorem sscanf_version_spec : sscanf_version_stmt.
Proof.
  unfold sscanf_version_stmt. intros until ev. intros TXT BY ST MI LO GT SPH TPV T0 TW T1 HT HP1 HP2 HP1q HP2q HP1t HP2t HP12 SSP ERR PC1 PC2.
  pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L40).
  assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (rewrite Htxt; unfold zlength; rewrite length_app; cbn; lia).
  assert (Hnul : znth txt (zlength pre) = 0%Z) by (rewrite Htxt; rewrite znth_app_r by (unfold zlength; lia); rewrite Z.sub_diag; reflexivity).
  assert (Hpre : forall i, (0 <= i < zlength pre)%Z -> znth txt i <> 0%Z).
  { intros i Hi. rewrite Htxt. rewrite znth_app_l by exact Hi. pose proof (proj1 (Forall_forall _ _) NZ (znth pre i) (znth_In pre i Hi)). cbv beta in H. lia. }
  destruct (sscanf_model_total txt (zlength pre) Hp Hnul Hpre BYT FMT_VERSION) as (r & HV & HR).
  unfold SSCANF_DEPTH in LO. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.

  assert (PC3 : rw_cells rsegs m (bv_unsigned sp - 8) [CB 0 []]).
  { clear - SPH GT LO. pose_word_ranges. unfold rw_cells, cells_at, bytes_at, wr_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize length app Z.of_nat].
    repeat split; try reflexivity; try exact I; try lia; intros i Hi; exfalso; lia. }
  eapply evt_mono.
  { eapply (sscanf_gen ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             T FA_VERSION txt pre post FMTL_VERSION [SW; SL 46; SW; SD] 2%Z 0%nat a4 P1 P2 (bv_unsigned sp - 8)%Z v1 v2 [] lo canary ev r);
      try eassumption; try LiaTuning.alia.
    - apply fmt_version_bytes. exact MI.
    - unfold FA_VERSION, FMTL_VERSION, zlength. cbn. lia.
    - unfold FMTL_VERSION. repeat constructor; lia.
    - exact fmt_enc_version.
    - cbn. lia.
    all: intros X; exfalso; clear -X; lia. }
  intros ms' PO. cbv beta in PO. unfold sscanf_post in PO. unfold sscanf2_post.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & ev' & w1 & w2 & w3 & E & REST).
  destruct REST as (MU & WM & MI' & ST' & BY' & SSP' & ERR' & PCa & PCb & PCc).
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [exact E|]. split; [exact HV|]. split; [cbn in HR; lia|].
  split. { eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x (O1 & O2 & O3 & O4 & _). repeat split; try assumption. clear - O1 LO. lia. }
  repeat (split; [eassumption|]). exact PCb.
Qed.
