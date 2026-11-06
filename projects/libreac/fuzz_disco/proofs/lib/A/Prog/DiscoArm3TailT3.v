(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its numbers changed; 391 of its 442 lines of code are new or changed and 445 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC81 YC85 YC4b DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacHuntRole ReacHuntVerdictName.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoRo DiscoArm3 DiscoArm3TailDefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c hunt_c reac_hunt_verdict_name_c slot_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition T3_H : nat := 531%nat.
Definition T3_U : nat := 532%nat.
Definition T3_A0 : nat := 540%nat.
Definition t3_rregs : list (bv 5) :=
  [1; 3; 4; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition t3_sr : list sv :=
  [SLit 0; SOff 533 0; SOff AT_A 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0;
   SOff 539 0; SOff AT_A 0; SOff 540 0; SOff 541 0; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0;
   SOff 546 0; SOff 547 0; SOff 32 0; SOff 548 0; SOff 549 0; SOff 550 0; SOff 551 0; SOff 552 0;
   SOff 553 0; SOff 554 0; SOff 555 0; SOff 556 0; SOff 557 0; SOff 558 0; SOff 559 0; SOff 560 0].
Definition t3_acs : list YP09.chunk := [YP09.mkChunk 152 (CVal 8 (SOff T3_H 440))].
Definition t3_hr : YP09.region := YP09.mkRegion (Some T3_H) 440 444 0 0 [YP09.mkChunk 440 (CVal 4 (SOff T3_U 0))].
Definition t3_fa : list (nat * afact) := [(T3_H, mkAF 4096 (2 ^ 47 - 480) 4); (T3_A0, mkAF 0 1 0)].
Definition t3_G : facts := d_facts t3_fa [].
Definition t3_mem : smem := map (fun r => set_window r 0 0) (d_kregions dsh_loop t3_acs []) ++ [t3_hr].
Definition t3_ss : sstate := mkSS HS_OFF t3_sr t3_mem None t3_G.
Definition t3_SH : list shent := [mkSHE T3_H 0 480].

Lemma t3_regs_ok : forall (E : env) (regs : bvmap 5 word),
  ew E AT_A = getr regs 2 -> ew E AT_A = getr regs 9 -> ew E 32 = getr regs 18 ->
  (forall (j : nat) (r : bv 5), nth_error t3_rregs j = Some r -> ew E (533 + j)%nat = getr regs r) ->
  regs_ok E t3_sr regs.
Proof.
  intros E regs H2 H9 H18 Hat. apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- _ = sv_denot ?Ex (sr_get ?srl ?rr) =>
        let v := eval vm_compute in (sr_get srl rr) in change (sr_get srl rr) with v end;
      first [ rewrite getr_zero; reflexivity
            | rewrite sv_denot_SOff0; symmetry;
              first [ exact H2 | exact H9 | exact H18
                    | lazymatch goal with |- ew _ ?nn = getr _ ?rr =>
                        let j := eval vm_compute in (nn - 533)%nat in exact (Hat j rr eq_refl) end ] ]
    | ]).
  destruct Hr.
Qed.

Lemma t3_sext : forall E u, ew E T3_U = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff T3_U 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
  intros E u Hu Hr. rewrite denot_lit_U, U_SExt, (U_atom E T3_U u Hu) by lia.
  change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small u) by lia. apply lit_canon.
Qed.

Lemma t3_narrow_sub : forall l x, submem (map (fun r => set_window r 0 0) l ++ x) (l ++ x).
Proof.
  induction l as [|r l IH]; intros x; cbn [map app].
  - apply submem_refl.
  - apply submem_keep; [|apply IH].
    unfold subregion, set_window. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc; exact Hc.
Qed.

Ltac t3_bvne := let Hq := fresh "Hq" in intro Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma t3_env_x : forall cx E (regs : bvmap 5 word) h u j r, nth_error t3_rregs j = Some r ->
  ew (d_env cx E ([Z_to_bv 64 h; Z_to_bv 64 u] ++ map (getr regs) t3_rregs)) (533 + j)%nat = getr regs r.
Proof.
  intros cx E regs h u j r Hj.
  assert (Hl : (j < length t3_rregs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  replace (533 + j)%nat with (AT_X + S (S j))%nat by (unfold AT_X; lia).
  rewrite d_env_x by (rewrite length_app, length_map; cbn [length] in *; lia).
  cbn [nth app]. apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity.
Qed.

Lemma t3_dE_hi : forall cx E k ws,
  d_E cx E -> (AT_FL <= k)%nat -> d_E cx (havoc E k ws).
Proof.
  intros cx E k ws (EE & E32 & HEI & E60 & EF & ESH) Hk. unfold d_E.
  rewrite !ew_havoc_old by (unfold AT_FL, AT_A, AT_F, AT_SH in *; lia).
  split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
  - intros nn r Hn. rewrite ew_havoc_old; [exact (EE nn r Hn)|].
    pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL in Hk. lia.
  - apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL in *; lia].
Qed.

Lemma t3_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
  - intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma t3_regs2 : forall (cx : dcx) (E : env) (R : bvmap 5 word),
  img_env VAL A_LIM E -> getr R 1 = Z_to_bv 64 (BASE + V_OFF) ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs))) (SLit 0 :: SOff A_TEXT V_OFF :: atom_regs 532 30) R.
Proof.
  intros cx E R HEI H1.
  assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
    by (apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
  regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                               | rewrite H1; symmetry; exact (codeptr_val _ V_OFF HEId) ]).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis DBPC : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis TVNAME : treac_hunt_verdict_name_spec B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.

Theorem a3t_T3 : a3t_step_spec (a3t_hs B MT XM_LIB RLO RHI tfib_K) (a3t_v B MT XM_LIB RLO RHI tfib_K).
Proof.
  intros cx h i n now W c Hhs.
  unfold a3t_hs, a3t_at, d_arm_at, d_at in Hhs.
  destruct Hhs as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HB & HJ & Hfr & Hk & Hnev & Hmo & Hacc & HP).
  destruct HP as (Hi & Hn & Hnow & HrL & (R19 & R10) & HX & Hsp0 & HBODY).
  pose proof HBODY as (T & G & Lk & H & HFRAME & HSHD & HOBJ & HBLK & HINP & HIMG & HFoff & HFstk & HFawr).
  pose proof HFRAME as (E & HE & HRG & HFL & V216 & V152).
  pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHl & HHg & HHok & _).
  pose proof HBLK as (HBperm & _ & _ & HBoff).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact HB | split; [exact HJ | exact Hfr]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
    as (HS16 & HSlo & HShi & HF4096 & HFceil & HFapp & HFimg & HF32 & HFpres & HFSpres & HSpres & HAR3 & Hfin & EFA & EFL).
  destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; pose proof asan_consts as (C1 & _); lia)) as (HAr & HA32).
  pose proof HrL as (RspA & R3 & R4 & R8 & R9 & R18 & R20 & R25).
  pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
  assert (HinH : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HBperm)). left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HinH) as (Hh16 & Hh4096 & Hhceil & Hhapp & Hhpres & _).
  change (req_size HUNT_SIZE) with 480 in Hhceil, Hhapp, Hhpres.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold MFRAME in HAr. unfold LLVMF_STK in HSlo.
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in *.
  pose proof (blk_off_imgP B ly3 S3 W mem3 md3 h HUNT_SIZE HAR3 HinH) as Hhimg.
  change (req_size HUNT_SIZE) with 480 in Hhimg.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE DFRAME_CLASS (c_fpos cx) HAR3 HinH Hfin) as HdHF.
  unfold zdisjoint in HdHF. cbn [fst snd] in HdHF. rewrite EFA in HdHF. change (req_size HUNT_SIZE) with 480 in HdHF.
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in HdHF.
  pose proof (pa_obj_img 1 ltac:(vm_compute; lia)) as HO1. pose proof (pa_obj_img 66 ltac:(vm_compute; lia)) as HO66.
  set (u := u_at H 440 4).
  assert (Ru : 0 <= u < 2 ^ 32).
  { unfold u, u_at. pose proof (disco_table.ble_range (sub H 440 4)) as R.
    rewrite (disco_table.length_sub H 440 4) in R by (try rewrite HHl; lia). exact R. }
  pose proof (hunt_val4 SEGS (rd W mem3) h H 440 HHg ltac:(lia) ltac:(rewrite HHl; lia)) as Mv.
  set (vals := [Z_to_bv 64 h; Z_to_bv 64 u] ++ map (getr regs) t3_rregs).
  assert (Lv : length vals = 30%nat) by (unfold vals; rewrite length_app, length_map; reflexivity).
  assert (EX : forall j r, nth_error t3_rregs j = Some r -> ew (d_env cx E vals) (533 + j)%nat = getr regs r)
    by (intros j r Hj; exact (t3_env_x cx E regs h u j r Hj)).
  assert (EHh : ew (d_env cx E vals) T3_H = Z_to_bv 64 h) by (exact (d_env_x cx E vals 0 ltac:(rewrite Lv; lia))).
  assert (EHu : ew (d_env cx E vals) T3_U = Z_to_bv 64 u) by (exact (d_env_x cx E vals 1 ltac:(rewrite Lv; lia))).
  assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn) by (intros nn Hnn; apply d_env_old; exact Hnn).
  assert (U2 : bv_unsigned (ew (d_env cx E vals) 2) = d_S cx)
    by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (U60 : bv_unsigned (ew (d_env cx E vals) AT_A) = d_A cx)
    by (rewrite EO by (unfold AT_FL, AT_A; lia); rewrite E60; apply unsigned_lit_small; lia).
  assert (U516 : bv_unsigned (ew (d_env cx E vals) AT_F) = d_FB cx)
    by (rewrite EO by (unfold AT_FL, AT_F; lia); rewrite EF; apply unsigned_lit_small; lia).
  assert (U529 : bv_unsigned (ew (d_env cx E vals) AT_SH) = shadow_addr (d_FB cx)).
  { rewrite EO by (unfold AT_FL, AT_SH; lia). rewrite ESH. apply unsigned_lit_small.
    unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (d_FB cx) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  assert (U32 : bv_unsigned (ew (d_env cx E vals) 32) = SHADOW_OFF)
    by (rewrite EO by (unfold AT_FL; lia); rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (UH : bv_unsigned (ew (d_env cx E vals) T3_H) = h) by (rewrite EHh; apply unsigned_lit_small; lia).
  assert (UO1 : bv_unsigned (ew (d_env cx E vals) (A_OBJ 1)) = VAL (A_OBJ 1))
    by (rewrite EO by (unfold AT_FL, A_OBJ; lia); apply HEI0; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (UO66 : bv_unsigned (ew (d_env cx E vals) (A_OBJ 66)) = VAL (A_OBJ 66))
    by (rewrite EO by (unfold AT_FL, A_OBJ; lia); apply HEI0; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (HS0 : st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) (ss_d HS_OFF t3_sr dsh_loop t3_acs [] [t3_hr] t3_G)
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + HS_OFF)) mem3 (YK11.seg_rom SEGS)))).
  { apply (DSEAT LAWS PAL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E HS_OFF t3_sr vals t3_acs [] [t3_hr] t3_G HC HE HRG HFL).
    - apply t3_regs_ok; [| | | exact EX].
      + rewrite EO by (unfold AT_A, AT_FL; lia). rewrite E60. unfold w64. rewrite <- RspA. unfold spZ.
        apply Z_to_bv_bv_unsigned.
      + rewrite EO by (unfold AT_A, AT_FL; lia). rewrite E60, R9. reflexivity.
      + rewrite EO by (unfold AT_FL; lia). rewrite E32, R18. reflexivity.
    - apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals t3_fa [] HC HE); [| exact I].
      cbn [t3_fa atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      assert (EA0 : ew (d_env cx E vals) T3_A0 = getr regs 10) by exact (EX 7%nat 10%bv eq_refl).
      rewrite UH, EA0.
      change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
      destruct R10 as [R10 | R10]; rewrite R10; unfold w64; rewrite unsigned_lit_small by lia;
        repeat split; lia.
    - constructor; [|constructor].
      apply (chunk_ok_val SEGS (d_env cx E vals) _ (d_A cx) 152 8 (SOff T3_H 440) (h + 440)).
      + cbn [sv_denot]. rewrite UH. reflexivity.
      + zside.
      + zside.
      + exact V152.
    - constructor.
    - constructor; [|constructor]. unfold region_ok, t3_hr.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UH.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ h 440 4 (SOff T3_U 0) u);
        [cbn [sv_denot]; rewrite EHu, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - constructor; [|constructor]. unfold d_kregions, t3_hr, fshadow_region, got_regionP, bcell_regionP.
      cbn [all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. unfold AT_STK.
      rewrite U2, U60, U516, U529, UH, UO1, UO66.
      change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
      unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hhapp.
      unfold off_img, IMG_LO, IMG_TOP in Hhimg. unfold IMG_LO, IMG_TOP in HO1, HO66.
      pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (d_FB cx) 8 (2 ^ 44 - 2 ^ 20) ltac:(lia) ltac:(lia)).
      repeat split; lia.
    - vm_compute. reflexivity. }
  assert (HS : st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) t3_ss
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + HS_OFF)) mem3 (YK11.seg_rom SEGS))))
    by exact (st_ok_pi_submem (fx := fq) _ _ _ t3_mem HS0 (t3_narrow_sub _ _) ltac:(vm_compute; reflexivity)).
  clear HS0.
  assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))).
  assert (SHOK : sh_ok SEGS (SOff 32 0) t3_SH (d_env cx E vals) (rd W mem3)).
  { unfold sh_ok, t3_SH. apply Forall_cons; [|apply Forall_nil].
    eapply shent_ok_of_range.
    - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W mem3 md3 h HUNT_SIZE h 480 HAR3 HinH ltac:(lia)
        ltac:(change (req_size HUNT_SIZE) with 480; lia)).
    - unfold U. cbn [sv_denot]. rewrite U32, Z.add_0_r. unfold SHADOW_OFF. apply YP0e.zcanon_id. unfold M64. lia.
    - unfold U. cbn [sv_denot]. rewrite UH, Z.add_0_r. apply YP0e.zcanon_id. unfold M64. lia.
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hhapp. lia. }
  pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
  unfold cfg_at, w64.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  assert (Emem : ms_mem ms = mem3).
  { apply functional_extensionality. intros x. apply HF. intros (r & Hr & Hw).
    vm_compute in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia|]). destruct Hr. }
  pmkst HS.
  rewrite Emem. rewrite Emem in HJ.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (10%bv : bv 5) HS) as Q10.
  replace (sr_get (ss_regs _) (10%bv : bv 5)) with (SExt true 32 (SOff T3_U 0)) in Q10 by (vm_compute; reflexivity).
  cbn [ms_regs restrict] in Q10.
  rewrite (t3_sext _ u EHu Ru) in Q10.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26.
  assert (X3 : ew (d_env cx E vals) 534 = getr regs 3) by exact (EX 1%nat 3%bv eq_refl).
  assert (X4 : ew (d_env cx E vals) 535 = getr regs 4) by exact (EX 2%nat 4%bv eq_refl).
  assert (X8 : ew (d_env cx E vals) 539 = getr regs 8) by exact (EX 6%nat 8%bv eq_refl).
  assert (X19 : ew (d_env cx E vals) 548 = getr regs 19) by exact (EX 15%nat 19%bv eq_refl).
  assert (X20 : ew (d_env cx E vals) 549 = getr regs 20) by exact (EX 16%nat 20%bv eq_refl).
  assert (X25 : ew (d_env cx E vals) 554 = getr regs 25) by exact (EX 21%nat 25%bv eq_refl).
  rewrite X3 in Q3. rewrite X4 in Q4. rewrite X8 in Q8. rewrite X19 in Q19. rewrite X20 in Q20. rewrite X25 in Q25.
  rewrite EO in Q2, Q9, Q18 by (unfold AT_FL; lia).
  change (ew E 60) with (ew E AT_A) in Q2, Q9. change 516%nat with AT_F in Q22, Q26.
  rewrite E60 in Q2, Q9. rewrite E32 in Q18. rewrite U516 in Q22, Q26.
  change (Z_to_bv 64 (d_FB cx + 2992)) with (w64 (d_obj cx OS)) in Q22.
  change (Z_to_bv 64 (d_FB cx + 2128)) with (w64 (d_obj cx OOUR)) in Q26.
  assert (Q2' : getr (ms_regs ms) 2 = getr regs 2).
  { rewrite Q2. unfold w64. rewrite <- RspA. unfold spZ. apply Z_to_bv_bv_unsigned. }
  rewrite <- R9 in Q9. rewrite <- R18 in Q18.
  clear Q2. rename Q2' into Q2.
  clear HS SHOK HF HFr HG Emem RUN.
  set (R := ms_regs ms) in *.
  set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md' k) by exact (conj HB (conj HJ Hfr)).
  assert (SpR : spZ R = d_A cx) by (unfold spZ in *; rewrite Q2; exact RspA).
  pose proof (DSEAT LAWS PAL fq cx dsh_loop ly3 S3 W R mem3 md' k E AF_reac_hunt_verdict_name
    (SLit 0 :: SOff A_TEXT V_OFF :: atom_regs 532 30) (map (getr R) (tl all_regs)) [] [] [] (d_facts [] [])
    HCTX HE HRG HFL (t3_regs2 cx E R HEI0 Q1)
    (DFACTS LAWS cx ly3 S3 W mem3 md' k E (map (getr R) (tl all_regs)) [] [] HCTX HE I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
  assert (HAFN : afn_pre SEGS B REAC_HUNT_VERDICT_NAME_STK ly3 S3 W (regupd R 8 (Z_to_bv 64 0)) mem3 md' []).
  { pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
    eapply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md' k (regupd R 8 (Z_to_bv 64 0)) REAC_HUNT_VERDICT_NAME_STK
      (d_A cx - d_S cx) [] HJ).
    - unfold spZ. rewrite getr_other by t3_bvne. fold (spZ R). rewrite SpR. lia.
    - pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
      rewrite HA32 in DA. rewrite HS16 in DS.
      replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult.
    - lia.
    - unfold REAC_HUNT_VERDICT_NAME_STK, ESTACK. lia.
    - unfold REAC_HUNT_VERDICT_NAME_STK, ESTACK, LLVMF_STK. lia.
    - rewrite getr_other by t3_bvne. rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite getr_other by t3_bvne. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
    - rewrite getr_other by t3_bvne. rewrite Q3. exact R3.
    - rewrite getr_other by t3_bvne. rewrite Q4. exact R4.
    - left. split; [|reflexivity]. left. unfold s0Z. rewrite getr_same by t3_bvne.
      rewrite unsigned_lit_small by lia. lia. }
  assert (Hvr : -2 ^ 31 <= bv_swrap 32 u < 2 ^ 31).
  { assert (HM : bv_half_modulus 32 = 2147483648) by reflexivity.
    assert (HMM : bv_modulus 32 = 4294967296) by reflexivity.
    unfold bv_swrap, bv_wrap. rewrite HM, HMM. pose proof (Z.mod_pos_bound (u + 2147483648) 4294967296 ltac:(lia)). lia. }
  pose proof (DCRO LAWS DROH ly3 S3 W mem3 md' (proj1 HJ) HIMG) as (_ & _ & _ & _ & _ & HVD & _).
  destruct HVD as (V1 & _ & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & _).
  assert (V2 : zseps [(VAL (A_OBJ 59), 24); (VAL (A_OBJ 1), 8); (VAL (A_OBJ 66), 8)]).
  { rewrite !pa_obj_val by (unfold disco_nobj; lia).
    let v := eval vm_compute in (disco_obj 59) in change (disco_obj 59) with v.
    let v := eval vm_compute in (disco_obj 1) in change (disco_obj 1) with v.
    let v := eval vm_compute in (disco_obj 66) in change (disco_obj 66) with v.
    cbn [zseps zseps_from fst snd]. lia. }
  rewrite pa_sigma_reac_hunt_verdict_name.
  eapply SRr_mono.
  { exact (TVNAME fq ly3 S3 W R mem3 md' [] (bv_swrap 32 u) HAFN Q10 Hvr V1 V2 V3 V4 V5 V6 V7 V8 V9 V10). }
  cbv beta. intros W2 c2 HW2 Hpost.
  unfold treac_hunt_verdict_name_post, apost_base in Hpost.
  destruct Hpost as (fq4 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hfreg4 & Hcsr4 & HJc & HP & Ha4 & Hne4 & Hstr4 & Ely & ES & EW & HPerm).
  subst ly4 S4 W2.
  pose proof (ajournal_sub SEGS B LAWS pa_segs_low LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md' k REAC_HUNT_VERDICT_NAME_STK (spZ R) [] [] ly3 S3 W mem4 md4 0 HJ HJc
    ltac:(rewrite SpR; unfold LLVMF_STK, REAC_HUNT_VERDICT_NAME_STK, ESTACK; lia) ltac:(rewrite SpR; lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ4.
  cbn [app] in HJ4. rewrite Z.add_0_r in HJ4.
  assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem4 md4 k) by exact (conj HB (conj HJ4 Hfr)).
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem4 md4 k HCTX4)
    as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _ & _ & K4 & _).
  assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply K1; [lia | rewrite SpR; lia]. }
  assert (KF : forall a, d_FB cx <= a < d_FB cx + 4096 -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [|exact (inFP_nil a)].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  assert (KS : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
    aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [|exact (inFP_nil a)].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (EA60 : ew E 60 = w64 (d_A cx)) by exact E60.
  assert (EA516 : ew E 516 = w64 (d_FB cx)) by exact EF.
  assert (EA529 : ew E 529 = w64 (shadow_addr (d_FB cx))) by exact ESH.
  assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
    by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
  jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W) mem4) HP [0;1;2;3]%nat HS2.
  match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
  { cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply (t3_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_S cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
      + intros a Ha. apply KA. lia.
      + intros a Ha. lia.
    - eapply (t3_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_A cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA60. unfold w64. apply unsigned_lit_small. lia.
      + intros a Ha. apply KA. lia.
      + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
    - eapply (t3_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_FB cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA516. unfold w64. apply unsigned_lit_small. lia.
      + intros a Ha. apply KF. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
      + intros a Ha. apply GFpres4. lia.
    - eapply (t3_kept _ (w_H W) (w_H W) mem3 mem4 _ (shadow_addr (d_FB cx))).
      + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA529. unfold w64. apply unsigned_lit_small.
        unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_le_upper_bound (d_FB cx) 8 (2 ^ 44 - 2 ^ 20) ltac:(lia) ltac:(lia)). lia.
      + intros a Ha. apply KS. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia.
      + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
        apply GFsh4. lia. }
  specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
  assert (HE2 : d_E cx (havoc (d_env cx E (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
    by (apply t3_dE_hi; [apply d_E_env; exact HE | unfold AT_FL; lia]).
  assert (HFL2 : ew (havoc (d_env cx E (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
    Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
    by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
  assert (KV : forall off v, 0 <= off <= 352 -> val_mem SEGS (mrestrict (w_H W) mem3) (d_A cx + off) 8 v ->
    val_mem SEGS (mrestrict (w_H W) mem4) (d_A cx + off) 8 v).
  { intros off v Hoff Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact Hv].
    intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
  pose proof (DLAND LAWS FFL fq cx h dsh_loop ly3 S3 W md4 k _ _
    (YK11.mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + 8964)) mem4 (YK11.seg_rom SEGS))
    HCTX4 HE2 HFL2 HS2 ltac:(vm_compute; reflexivity) (KV 216 h ltac:(lia) V216) (KV 152 (h + 440) ltac:(lia) V152))
    as (HFRM4 & HSHD4).
  pose proof (DBPC LAWS DROH DCAN cx h n [] dsh_loop dsh_loop ly3 S3 W mem3 md' ly3 S3 W mem4 md4 k REAC_HUNT_VERDICT_NAME_STK
    (spZ R) [] 0 HBODY (conj HB HJ4) HJc
    ltac:(rewrite SpR; unfold LLVMF_STK, REAC_HUNT_VERDICT_NAME_STK, ESTACK; lia) ltac:(rewrite SpR; lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
    ltac:(intros (a & Ha & _); exfalso; exact (inFP_nil a Ha))
    HPerm HFRM4 HSHD4) as HBODY4.
  assert (P2 : getr regs4 2 = getr regs 2) by (transitivity (getr R 2); [exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact Q2]).
  assert (P3 : getr regs4 3 = getr regs 3) by (transitivity (getr R 3); [exact (HP 3 ltac:(unfold acallee_saved; lia)) | exact Q3]).
  assert (P4 : getr regs4 4 = getr regs 4) by (transitivity (getr R 4); [exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact Q4]).
  assert (P8 : getr regs4 8 = getr regs 8) by (transitivity (getr R 8); [exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact Q8]).
  assert (P9 : getr regs4 9 = getr regs 9) by (transitivity (getr R 9); [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact Q9]).
  assert (P18 : getr regs4 18 = getr regs 18) by (transitivity (getr R 18); [exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact Q18]).
  assert (P19 : getr regs4 19 = getr regs 19) by (transitivity (getr R 19); [exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact Q19]).
  assert (P20 : getr regs4 20 = getr regs 20) by (transitivity (getr R 20); [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact Q20]).
  assert (P22 : getr regs4 22 = w64 (d_obj cx OS)) by (transitivity (getr R 22); [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact Q22]).
  assert (P25 : getr regs4 25 = getr regs 25) by (transitivity (getr R 25); [exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact Q25]).
  assert (P26 : getr regs4 26 = w64 (d_obj cx OOUR)) by (transitivity (getr R 26); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact Q26]).
  pose proof HX as ((H232 & H344) & H224 & H248).
  unfold a3t_v, a3t_at, d_arm_at, d_at.
  exists fq4, ly3, S3, regs4, mem4, md4, k, acc.
  split; [unfold cfg_at, w64; rewrite Q1; reflexivity|].
  split; [destruct Hcsr4 as [Hc | Hc]; [rewrite Hc; exact Hfrm0 | exact Hc]|].
  split; [exact HB|]. split; [exact HJ4|]. split; [exact Hfr|].
  split; [exact Hk|]. split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { split; [unfold spZ in *; rewrite P2; exact RspA|].
    split; [rewrite P3; exact R3|]. split; [rewrite P4; exact R4|]. split; [rewrite P8; exact R8|].
    split; [rewrite P9; exact R9|]. split; [rewrite P18; exact R18|]. split; [rewrite P20; exact R20|].
    rewrite P25; exact R25. }
  split.
  { split; [|exact Hne4]. split; [rewrite P19; exact R19|]. split; [exact P22 | exact P26]. }
  split.
  { split; [split|split].
    - apply KV; [lia | exact H232].
    - apply KV; [lia | exact H344].
    - apply KV; [lia | exact H224].
    - apply KV; [lia | exact H248]. }
  split.
  { split; [apply KV; [lia | exact H232] | apply KV; [lia | exact H344]]. }
  exact HBODY4.
Qed.

End h.
End f.
End d.
