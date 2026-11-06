(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedSetupC), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AD27.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedSetupC.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySchedSetupC.v, ported from a working branch 7c8c67da870 (blob bbef4597855): image B's register file (the bytes left in s7, the cursor in s11, the scene's base in s5 and then s7, the count in s4), the shadow base reloaded from spill slot 144 before each check, the UBSan pointer-overflow guard before each input read (decided by the cursor's interval), the table as atom 42 of the environment, objects 35 / 36 for image A's 32 / 33, blk_off_imgB with IMG_LO_B / IMG_TOP_B for image A's off_img, and a seat whose shadow region has no chunks, so that the eighteen shadow stores run on a closed state. *)

(* Segment C of the scheduler's setup in fuzz_grant's entry function
   LLVMFuzzerTestOneInput on the ASan+UBSan build (image B, LLVMFEntrySchedSetupDefs.v):
   from the return of reac_headamp_tx_set_resweep at 0x81a50 to the return of
   __asan_memset at 0x81b1c (fuzz_grant.c:394-395).

   The block reads the frame count's two bytes (0x81a74, 0x81ab8) while bytes are left,
   each after a pointer-overflow guard whose taken side is the trap 0x81f48 (0x81a5c,
   0x81a9c) and after the shadow byte of its address (0x81a6c, 0x81ab0), marks
   `unset_sent` (F+576, 144 bytes) usable (shadow bytes 72..89 of the frame, 0x81ac0 ..
   0x81b08) and zeroes it with __asan_memset (0x81b18). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC81 YC4b YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
YC1g YC1h YC1i YC45 YC85 GrantACjr ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySchedSetupDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel GrantSlotPlan SlotNeeds_c Seg_sched_setup SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The register file at 0x81a50 (atoms as in LLVMFEntrySchedSetupDefs.v): sp and s1 the
   realigned stack pointer, s0 the caller's sp, gp and tp as at entry, s3 the frame's
   shadow; s11 is `r27` (the cursor, SCH_P + 6, when bytes are left); the others their
   own atoms (s5 the scene's base, s7 the bytes left, s8 the scene's width). *)
Definition schc_sr (r27 : sv) : list sv :=
  [ SLit 0; SOff 531 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 535 0; SOff 536 0; SOff 537 0;
    SOff 2 0; SOff 60 0; SOff 540 0; SOff 541 0; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0;
    SOff 546 0; SOff 547 0; SOff 548 0; SOff 529 0; SOff 550 0; SOff 551 0; SOff 552 0; SOff 553 0;
    SOff 554 0; SOff 555 0; SOff 556 0; r27; SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0 ].

(* The machine state at 0x81a50, seated: the frame read-only, its shadow region with an
   empty write window and NO chunks (the walk never reads the frame's shadow, and the
   eighteen stores of 0x81ac0 .. 0x81b08 then run on a closed state), the spill slots
   the block reads as atoms, the input's first `m` bytes from SCH_P on. *)
Definition schc_ss0 (r27 : sv) (m : nat) : sstate :=
  mkSS GP_sch2 (schc_sr r27)
    (ge_saved_region :: sch_spill :: set_window (ge_frame_region []) 0 0
     :: ge_shadow_region 0 0 [] :: ge_obj_regions ++ sch_ex m) None sch_G.

Lemma schc_sv_off : forall (E : env) n x c, ew E n = Z_to_bv 64 x -> sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n x c H. cbn [sv_denot]. rewrite H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* s5 = b7 << 8 and s4 = s5 | b6, the frame count's two bytes (0x81abc, 0x81b00). *)
Lemma schc_U_hi : forall (E : env) b7, ew E 41 = Z_to_bv 64 b7 -> 0 <= b7 < 256 ->
  U E (SAlu ALU_SLL (SOff 41 0) (SLit 8)) = 256 * b7.
Proof.
intros E b7 H Hb. rewrite U_SAlu, U_SLit, (U_atom_off E 41 b7 0 H) by lia. cbn [zalu_raw].
change (Z.land (zcanon 8) 63) with 8. rewrite Z.add_0_r, Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma schc_U_or : forall (E : env) b6 b7, ew E 40 = Z_to_bv 64 b6 -> ew E 41 = Z_to_bv 64 b7 ->
  0 <= b6 < 256 -> 0 <= b7 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 41 0) (SLit 8)) (SOff 40 0)) = b6 + 256 * b7.
Proof.
intros E b6 b7 H6 H7 B6 B7. rewrite U_SAlu, (schc_U_hi E b7 H7 B7), (U_atom_off E 40 b6 0 H6) by lia.
cbn [zalu_raw]. rewrite Z.add_0_r, Seg_sched_setup.lor256 by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* The frame's shadow at 0x81b1c is the one at 0x81a50 with bytes 72..89 (unset_sent) 0. *)
Lemma schc_gsh : forall i, (i < 104)%nat ->
  nth i GSH_sched 0 = if ((72 <=? i) && (i <? 90))%nat then 0 else nth i GSH_c 0.
Proof.
assert (H : forallb (fun i => Z.eqb (nth i GSH_sched 0)
                 (if ((72 <=? i) && (i <? 90))%nat then 0 else nth i GSH_c 0)) (seq 0 104) = true)
  by (vm_compute; reflexivity).
intros i Hi. rewrite forallb_forall in H.
specialize (H i (proj2 (in_seq 104 0 i) ltac:(lia))). apply Z.eqb_eq in H. exact H.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* RT_MEMSET of GrantBContracts.v. *)
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Let RUN := paj_run B LAWS.
Let RUNP := SRr_run_pi_AJ (L := grant_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := grant_listing) B LAWS.

(* A phase's machine state, seated with a shadow region that has no chunks: the
   shadow bytes are not read (`gshadow cx fp W3 ms3 []` holds trivially), so nothing
   about them enters the symbolic state (lib/A/Prog/GrantEntryEndFree.v's fresh seat). *)
Lemma schc_seat0 : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3 E pc sr sh extra G,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] ->
  ge_E cx fp E -> img_env VAL A_LIM E ->
  ge_body cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  YP09.regions_wf (ge_regions cx fp [] (ge_slot_chunks []) [] 0 0 extra) = true ->
  Forall (YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3))) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (ge_regions0 cx fp [] (ge_slot_chunks []) [] 0 0) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (ge_ss cx fp pc sr [] (ge_slot_chunks []) [] 0 0 extra G) (restrict (w_H W3) ms3).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 E pc sr sh extra G HB HJ Hfrs HE HEI HBD HR Hwf Hex Hexp Hexd HG.
pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & Hgregs & Hsaved & Hshadow
                   & Hflag & Hlen & Hgarr).
assert (HSH0 : gshadow cx fp W3 ms3 []) by (intros i Hi; cbn [length] in Hi; lia).
assert (Hms : restrict (w_H W3) ms3 =
              mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W3) (ms_mem ms3))
                   (seg_rom SEGS)).
{ clear -Hpc Hresv Hpend Hrom Hfregs Hfcsr.
  destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
    in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
  subst. reflexivity. }
rewrite Hms. unfold ge_ss, ge_regions.
apply pa_entry_st_ok_full; [exact HR | exact Hwf | | | exact HG].
- apply Forall_app. split; [|exact Hex].
  unfold ge_regions0.
  apply Forall_cons; [eapply ge_region_saved with (W3 := W3) (ms3 := ms3); eassumption|].
  apply Forall_cons; [eapply ge_region_spill with (W3 := W3) (ms3 := ms3);
                      first [eassumption | apply Forall_nil]|].
  apply Forall_cons; [eapply ge_region_frame with (W3 := W3) (ms3 := ms3);
                      first [eassumption | apply Forall_nil]|].
  apply Forall_cons; [eapply ge_region_shadow with (W3 := W3) (ms3 := ms3);
                      first [eassumption | lia]|].
  eapply ge_region_objs with (W3 := W3) (ms3 := ms3); eassumption.
- apply ge_pwd_app; [|exact Hexp | exact Hexd].
  eapply ge_disj with (W3 := W3) (ms3 := ms3); eassumption.
Qed.

Lemma schc_seat : forall cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 (m : nat) (r27 : sv) (t : Z),
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] ->
  sch_common B MT cx fp GP_sch2 GSH_c k acc ly3 S3 W3 ms3 t ->
  (m <= 8)%nat -> Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx)) + Z.of_nat m <= c_n cx ->
  getr (ms_regs ms3) 27 = sv_denot (sch_env cx fp t (ms_regs ms3)) r27 ->
  st_ok_pi SEGS VAL (sch_env cx fp t (ms_regs ms3)) (schc_ss0 r27 m) (restrict (w_H W3) ms3).
Proof.
intros cx fp k acc ly3 S3 W3 ms3 md3 m r27 t HB HJ Hfrs HC Hm8 Hmn H27.
destruct HC as (Hbody & _ & _ & Hblk & _ & R19 & _ & _ & S40 & S48 & _ & _ & S96 & S112 & _ & S136
                & S144 & S152 & _).
pose proof Hbody as (_ & _ & _ & _ & _ & _ & Hgr & _ & _ & _ & _ & Hinp).
pose proof Hgr as (R2 & R8 & R9 & R3 & R4).
pose proof HB as (HPRE & H10 & H11 & Hpn & _ & _ & _ & _ & _ & _ & HE0 & Husp & H32 & _).
pose proof HJ as (HAR & _).
pose proof (ge_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (HF0 & HFc & HFia & HFo & HSHeq).
pose proof (ge_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (Hs0 & Hs1).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof IMG_LO_B_val as HIL. pose proof IMG_TOP_B_val as HIT.
pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 1 ltac:(lia)) as Ho1.
pose proof (pa_obj_img 35 ltac:(lia)) as Ho35. pose proof (pa_obj_img 36 ltac:(lia)) as Ho36.
assert (Hsp1m : c_sp1 cx mod 32 = 0).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1d & _). rewrite Hs1d. rewrite Z.mul_comm. apply Z_mod_mult. }
assert (Hsp0r : 0 <= spZ (c_regs cx) < 2 ^ 64) by apply u64_range.
(* the input cursor *)
assert (HP : 4096 <= SCH_P cx /\ SCH_P cx + Z.of_nat m <= 140737479966720 /\
             (m <> 0%nat -> In (c_p cx, c_n cx) (ablocks B ly3 S3))).
{ unfold SCH_P. destruct Hpn as [(Hn0 & Hp0) | (Hn0 & Hin0)].
  - unfold c_n in Hn0, Hmn. assert (Hm0 : m = 0%nat) by lia. subst m.
    pose proof (Seg_sched_setup.pos_raw_le (c_pl cx)) as Hpr.
    rewrite Hp0. unfold GE_EMPTY, GrantBContracts.A_EMPTY_B. cbn [Z.of_nat] in *.
    assert (Hz : GrantSlotPlan.pos_raw (c_pl cx) = 0%nat) by lia. rewrite Hz. cbn [Z.of_nat].
    split; [lia|]. split; [lia | intros H; exfalso; exact (H eq_refl)].
  - assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; left; exact Hin0).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos' (c_n cx) ltac:(lia)) as [_ Hrq].
    split; [lia|]. split; [lia | intros _; exact Hin]. }
destruct HP as (HP0 & HP1 & HPin).
revert H27. remember (sch_env cx fp t (ms_regs ms3)) as E eqn:HEdef. intros H27.
assert (HE : ge_E cx fp E) by (subst E; apply (sch_env_E B MT); exact HB).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E33 : ew E 33 = Z_to_bv 64 (SCH_P cx)) by (subst E; apply sch_env_33).
assert (E42 : ew E 42 = Z_to_bv 64 t) by (subst E; apply sch_env_42).
assert (EB : forall j, (j < 8)%nat -> ew E (34 + j) = Z_to_bv 64 (sbat (c_pl cx) j)) by (subst E; apply sch_env_b).
assert (EREG : forall r : bv 5, (Z.to_nat (bv_unsigned r) <> 0)%nat -> ew E (530 + Z.to_nat (bv_unsigned r)) = getr (ms_regs ms3) r)
  by (subst E; apply sch_env_reg).
clear HEdef.
pose proof HE as (AG & E32 & E60 & E516 & E528 & E529).
unfold GA_SB, GA_SP1, GA_F, GA_FL, GA_FSH in E32, E60, E516, E528, E529.
(* the table's bounds *)
assert (HinT : In (t, 460) (ablocks B ly3 S3))
  by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinT) as (_ & Ht4096 & Htceil & Htapp & _).
change (req_size 460) with 460 in Ht4096, Htceil, Htapp.
(* the register file *)
assert (HREG : regs_ok E (schc_sr r27) (ms_regs ms3)).
{ assert (P2 : getr (ms_regs ms3) 2 = sv_denot E (SOff 60 0)) by (rewrite ge_sv_SOff0, E60; exact R2).
  assert (P9 : getr (ms_regs ms3) 9 = sv_denot E (SOff 60 0)) by (rewrite ge_sv_SOff0, E60; exact R9).
  assert (P8 : getr (ms_regs ms3) 8 = sv_denot E (SOff 2 0)).
  { rewrite ge_sv_SOff0, (AG 2%nat ltac:(lia)), (HE0 2%nat 2%bv eq_refl), R8. unfold w64, spZ. apply Z_to_bv_bv_unsigned. }
  assert (P3 : getr (ms_regs ms3) 3 = sv_denot E (SOff 3 0))
    by (rewrite ge_sv_SOff0, (AG 3%nat ltac:(lia)), (HE0 3%nat 3%bv eq_refl); exact R3).
  assert (P4 : getr (ms_regs ms3) 4 = sv_denot E (SOff 4 0))
    by (rewrite ge_sv_SOff0, (AG 4%nat ltac:(lia)), (HE0 4%nat 4%bv eq_refl); exact R4).
  assert (P19 : getr (ms_regs ms3) 19 = sv_denot E (SOff 529 0)) by (rewrite ge_sv_SOff0; rewrite E529; exact R19).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r) =>
        let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
      first [ exact P2 | exact P9 | exact P8 | exact P3 | exact P4 | exact P19 | exact H27
            | rewrite getr_zero; reflexivity
            | lazymatch goal with |- getr _ ?r = _ =>
                rewrite ge_sv_SOff0; symmetry; exact (EREG r ltac:(vm_compute; discriminate)) end ]
    | ]).
  destruct Hr. }
(* the fresh seat: the shadow region holds no chunks *)
assert (HS0 : st_ok_pi SEGS VAL E (ge_ss cx fp GP_sch2 (schc_sr r27) [] (ge_slot_chunks []) [] 0 0 (sch_ex m) sch_G)
                (restrict (w_H W3) ms3)).
{ apply (schc_seat0 cx fp k ly3 S3 W3 ms3 md3 E GP_sch2 (schc_sr r27) GSH_c (sch_ex m) sch_G
           HB HJ Hfrs HE HEI Hbody HREG).
  - unfold ge_regions. rewrite regions_wf_app. apply andb_true_intro. split; [vm_compute; reflexivity|].
    destruct m as [|m']; [reflexivity|]. cbn [sch_ex YP09.regions_wf]. rewrite rin_wf. reflexivity.
  - destruct m as [|m']; cbn [sch_ex]; [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
    specialize (HPin ltac:(discriminate)).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HPin) as (_ & Hp4096 & Hpceil & _).
    unfold YP09.region_ok, rin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. unfold rin_chunks in Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    apply (chunk_ok_val SEGS E _ (SCH_P cx) (Z.of_nat j) 1 (SOff (34 + j) 0) (sbat (c_pl cx) j)).
    + rewrite ge_sv_SOff0, (EB j ltac:(lia)). reflexivity.
    + pose proof (sbat_range (c_pl cx) j). change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    + cbn. lia.
    + set (pr := GrantSlotPlan.pos_raw (c_pl cx)) in *.
      assert (Hj' : (pr + j < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat)
        by (rewrite length_map; unfold c_n in Hmn; lia).
      destruct (Hinp (pr + j)%nat Hj') as [Hv _].
      unfold SCH_P. fold pr.
      replace (c_p cx + Z.of_nat pr + Z.of_nat j) with (c_p cx + Z.of_nat (pr + j)) by lia.
      replace (sbat (c_pl cx) j) with (nth (pr + j) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0); [exact Hv|].
      unfold sbat. fold pr. rewrite Seg_sched_setup.bat_in by (rewrite length_map in Hj'; exact Hj').
      unfold GrantSlotPlan.pbz. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hj'.
      apply (map_nth (fun b : byte => bv_unsigned b)).
  - destruct m as [|m']; cbn [sch_ex YP09.pairwise_disjoint YP09.all_disjoint]; repeat split.
  - destruct m as [|m']; cbn [sch_ex].
    + apply Forall_forall. intros r _. exact I.
    + specialize (HPin ltac:(discriminate)).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HPin) as (_ & Hp4096 & Hpceil & Hpapp & _).
      pose proof (req_size_pos' (c_n cx) ltac:(lia)) as [_ Hrq].
      pose proof (blk_off_imgB B ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR HPin) as Hpimg.
      pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ GE_CID fp HAR HPin
                    (ge_fin fp S3 Hfrs)) as Hpf.
      rewrite (ge_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) in Hpf.
      change (fs_frame_bytes GE_CID) with 1024 in Hpf. unfold zdisjoint in Hpf. cbn [fst snd] in Hpf.
      assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> YP09.base_val E (Some n) = VAL n).
      { intros n Hn. cbn [YP09.base_val]. rewrite (img_env_atomP E n HEI Hn). apply unsigned_lit_small. apply pa_val_range. }
      pose proof (ge_base_sp B MT cx fp HB E HE) as Ub2.
      unfold ge_regions0, ge_saved_region, ge_spill_region, ge_frame_region, fframe_region,
        ge_shadow_region, fshadow_region, ge_obj_regions, got_regionP, bcell_regionP,
        uar_got_regionP, uar_cell_regionP, rin.
      repeat apply Forall_cons; try apply Forall_nil;
        cbn [YP09.all_disjoint]; (split; [|exact I]); unfold YP09.extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi].
      all: rewrite ?Ub2, ?(EA (A_OBJ 1)), ?(EA (A_OBJ 35)), ?(EA (A_OBJ 0)), ?(EA (A_OBJ 36))
             by (unfold A_OBJ, A_TEXT, A_LIM; lia).
      all: cbn [YP09.base_val]; rewrite ?E33, ?E60, ?E516, ?E529; unfold GA_SP1, GA_F, GA_FSH in *;
        rewrite ?E60, ?E516, ?E529.
      all: unfold w64; rewrite ?unsigned_lit_small by lia; change (fs_frame_bytes GE_CID) with 1024;
        change (1024 / 8) with 128; rewrite ?HSHeq.
      all: unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, SCH_P in *; lia.
  - split; [|split; exact I].
    unfold sch_G, sch_atoms. cbn [f_atoms app map seq atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, E33, E60, !EB by lia.
    pose proof (sbat_range (c_pl cx) 0) as B0. pose proof (sbat_range (c_pl cx) 1) as B1.
    pose proof (sbat_range (c_pl cx) 2) as B2. pose proof (sbat_range (c_pl cx) 3) as B3.
    pose proof (sbat_range (c_pl cx) 4) as B4. pose proof (sbat_range (c_pl cx) 5) as B5.
    pose proof (sbat_range (c_pl cx) 6) as B6. pose proof (sbat_range (c_pl cx) 7) as B7.
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
    change (2 ^ 5) with 32. unfold SCH_SB, SHADOW_OFF.
    revert B0 B1 B2 B3 B4 B5 B6 B7 HP0 HP1 Hlo Hhi Hsp1 Hsp1m C1. clear. intros.
    repeat match goal with |- _ /\ _ => split end; lia. }
(* the spill slots the block reads, as atoms; the frame read-only *)
pose proof (st_ok_pi_region_nth E _ _ 2%nat _ HS0 eq_refl) as RF.
assert (RS : YP09.region_ok SEGS E (ms_mem (restrict (w_H W3) ms3)) sch_spill).
{ cbn [ms_mem restrict]. unfold YP09.region_ok, sch_spill.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite E60, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (V516 : forall c, sv_denot E (SOff 516 c) = Z_to_bv 64 (gF cx fp + c))
    by (intros c; cbn [sv_denot]; rewrite E516; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  assert (VR : forall v, 0 <= v < 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N 8)) by (intros v Hv; exact Hv).
  assert (V8 : Z.of_N 8 <= 8) by (cbn; lia).
  unfold GO_UNSET, GO_VAL, GO_PAR, GO_WAS in *.
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 40 8 (SOff 516 576) (gF cx fp + 576)); [rewrite V516; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S40).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 48 8 (SOff 33 0) (SCH_P cx)); [rewrite ge_sv_SOff0, E33; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S48).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 96 8 (SOff 516 816) (gF cx fp + 816)); [rewrite V516; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S96).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 516 800) (gF cx fp + 800)); [rewrite V516; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S112).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 136 8 (SOff 516 32) (gF cx fp + 32)); [rewrite V516; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S136).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 144 8 (SOff 32 0) SHADOW_OFF);
      [rewrite ge_sv_SOff0, E32; reflexivity | apply VR; unfold SHADOW_OFF; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S144).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 152 8 (SOff 42 0) t); [rewrite ge_sv_SOff0, E42; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S152). }
pose proof (ast_ok_pi_set_region E _ _ 1%nat _ sch_spill HS0 eq_refl eq_refl
  ltac:(unfold ge_ss, ge_regions; cbn [ss_mem list_upd ge_regions0 app]; cbn [YP09.regions_wf];
        rewrite regions_wf_app; apply andb_true_intro; split; [vm_compute; reflexivity|];
        destruct m as [|m']; [reflexivity|]; cbn [sch_ex YP09.regions_wf]; rewrite rin_wf; reflexivity) RS) as HS1.
pose proof (ast_ok_pi_set_region E _ _ 2%nat _ (set_window (ge_frame_region []) 0 0) HS1 eq_refl eq_refl
  ltac:(unfold ge_ss, ge_regions; cbn [ss_mem ss_pc ss_regs ss_resv ss_facts list_upd ge_regions0 app]; cbn [YP09.regions_wf];
        rewrite regions_wf_app; apply andb_true_intro; split; [vm_compute; reflexivity|];
        destruct m as [|m']; [reflexivity|]; cbn [sch_ex YP09.regions_wf]; rewrite rin_wf; reflexivity)
  (region_ok_rewindow SEGS E _ _ 0 0 RF ltac:(intros o Ho; lia))) as HS2.
exact HS2.
Qed.

(* ---- the memory from 0x81a50 to the return of __asan_memset ---- *)
Lemma schc_kept : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma schc_rdword : forall (H : word -> bool) (m m' : word -> option byte) a v,
  (forall i, 0 <= i < 8 -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
  rdword (aview SEGS H m) a = Some v -> rdword (aview SEGS H m') a = Some v.
Proof.
intros H m m' a v K Hr.
pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
pose proof (K 7 ltac:(lia)) as K7.
unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

(* ---- the call of __asan_memset (0x81b18) and the cut at its return ---- *)
(* At the wrapper's entry the walk from 0x81a50 has changed only the shadow bytes 72..89
   of the frame (now 0), and the registers hold the frame count's bytes. *)
Lemma schc_land : forall POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) (regsT : bvmap 5 word) memT mdT t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  sch_common B MT cx fp GP_sch2 GSH_c k acc ly3 S3 W3 ms3 t ->
  gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_sched0 (c_pl cx)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (gSH cx fp + 72 <= a < gSH cx fp + 90) ->
     aview SEGS (w_H W3) memT a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall i, 72 <= i < 90 -> aview SEGS (w_H W3) memT (gSH cx fp + i) = Some 0) ->
  getr regsT 10 = w64 (gF cx fp + GO_UNSET) -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 144 ->
  getr regsT 1 = w64 (BASE + GP_sch3) ->
  getr regsT 2 = w64 (c_sp1 cx) -> getr regsT 8 = w64 (spZ (c_regs cx)) -> getr regsT 9 = w64 (c_sp1 cx) ->
  getr regsT 3 = getr (c_regs cx) 3 -> getr regsT 4 = getr (c_regs cx) 4 ->
  getr regsT 18 = w64 (sch_b cx 6) -> getr regsT 20 = w64 (sch_b cx 6 + 256 * sch_b cx 7) ->
  getr regsT 21 = w64 (256 * sch_b cx 7) -> getr regsT 23 = w64 (sch_b cx 0) ->
  getr regsT 24 = w64 (sch_b cx 1) -> getr regsT 19 = w64 (gSH cx fp) ->
  getr regsT 22 = w64 (gF cx fp + GO_CH) ->
  ge_from B MT POST (GI_sch3 B MT) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS___asan_memset)) memT (seg_rom SEGS)) mdT) (POST cx).
Proof.
intros POST cx fp k acc ly3 S3 W3 ms3 regsT memT mdT t HB HJT Hfrs Hmo HC Htab KT ZT
  T10 T11 T12 T1 T2 T8 T9 T3 T4 T18 T20 T21 T23 T24 T19 T22 HN.
pose proof HC as (Hbody & Hk & Hacc & Hblk & Hn26 & R19 & R22 & S8 & S40 & S48 & S64 & S72 & S96 & S112
                  & S128 & S136 & S144 & S152 & Hwas & Hset & Hrel & HI1).
pose proof Hbody as (_ & _ & _ & _ & _ & _ & _ & Hsv & Hsh & Hflg & Hlen & Hinp).
pose proof (ge_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
pose proof (ge_F_facts B MT LAWS cx fp W3 (mkst regsT (Z_to_bv 64 (SIGMA GS___asan_memset)) memT (seg_rom SEGS))
              ly3 S3 mdT k HB HJT Hfrs) as (HF0 & HFc & HFia & HFo & HSHeq).
pose proof (ge_frame_addr_eq B MT LAWS cx fp W3 (mkst regsT (Z_to_bv 64 (SIGMA GS___asan_memset)) memT (seg_rom SEGS))
              ly3 S3 mdT k HB HJT) as EFA.
pose proof HB as (HPRE & _ & _ & Hpn & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJT as (HART & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp HART (ge_fin fp S3 Hfrs)) as (HF32 & _).
rewrite EFA in HF32.
assert (Hsp1m : c_sp1 cx mod 32 = 0).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1d & _). rewrite Hs1d. rewrite Z.mul_comm. apply Z_mod_mult. }
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
(* the frame, its shadow and the stack below s1 lie apart *)
assert (HG : 0x7fff8000 <= gSH cx fp /\ gSH cx fp + 128 <= 0x10007fff8000 /\ gSH cx fp + 128 <= c_sp1 cx - 4096 /\
             (gF cx fp + 1024 <= gSH cx fp \/ gSH cx fp + 128 <= gF cx fp) /\ gF cx fp + 1024 <= c_sp1 cx - 4096).
{ rewrite HSHeq. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  revert HF0 HFc HFia Hlo Hsp1 C1. clear. intros. lia. }
destruct HG as (HG1 & HG2 & HG3 & HG4 & HG5).
(* a heap block the phase holds lies apart from all three *)
assert (HBK : forall p n, In (p, n) (ablocks B ly3 S3) -> forall i, 0 <= i < n ->
          0 <= p + i < 2 ^ 64 /\ ~ (gSH cx fp + 72 <= p + i < gSH cx fp + 90) /\
          ~ (gF cx fp + 576 <= p + i < gF cx fp + 720) /\ ~ (c_sp1 cx - 4096 <= p + i < c_sp1 cx)).
{ intros p n Hin i Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HART Hin) as (_ & Hp4096 & Hpceil & Hpapp & _).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 memT mdT _ _ GE_CID fp HART Hin (ge_fin fp S3 Hfrs)) as Hpf.
  rewrite EFA, Hfb in Hpf. unfold zdisjoint in Hpf. cbn [fst snd] in Hpf.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Hpapp.
  revert Hp4096 Hpceil Hpapp Hrq Hpf Hi HG1 HG2 HG3 HG5 Hlo Hsp1 C1. clear. intros. lia. }
eapply SRr_bind.
{ apply (aj_intrin_at SEGS B LAWS pa_segs_low OSet (SIGMA GS___asan_memset) AMEMSET W3 regsT memT
     GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 mdT k
     (gF cx fp + 576) 0 144 (c_sp1 cx - spZ (c_regs cx)) (w64 (BASE + GP_sch3)) HJT).
  - rewrite T10. reflexivity.
  - exact T11.
  - exact T12.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite T2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - revert Hsp1m Hal16. clear. intros. lia.
  - lia.
  - unfold ESTACK, GE_STK, GrantBContracts.STK_LLVMFuzzerTestOneInput. lia.
  - rewrite T3. exact Hgp.
  - rewrite T4. exact Htp.
  - exact T1.
  - unfold w64, GP_sch3. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite EFA, Hfb. lia.
    + unfold ESTACK. lia.
  - revert HFia HFc C1. clear. unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd.
    intros. lia.
  - apply zero_shadow_range; [revert HF32; clear; intros; lia | reflexivity |].
    intros i Hi. change (144 / 8) with 18 in Hi.
    replace (shadow_of_addr SHADOW_OFF (gF cx fp + 576) + i) with (gSH cx fp + (72 + i))
      by (unfold shadow_of_addr; rewrite HSHeq; revert HF32; clear; intros; lia).
    apply ZT. lia.
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 memT mdT GE_CID fp (gF cx fp + 576) 144 HART
                        (ge_fin fp S3 Hfrs)); rewrite ?EFA, ?Hfb; lia.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Heff & Hfr & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (gF cx fp + 576 <= a < gF cx fp + 720) -> ~ (c_sp1 cx - 4096 <= a < c_sp1 cx) ->
             aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memT a).
{ intros a Ha H1 H2. apply Hfr; [exact Ha | lia | unfold ESTACK; lia]. }
assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (gSH cx fp + 72 <= a < gSH cx fp + 90) ->
             ~ (gF cx fp + 576 <= a < gF cx fp + 720) -> ~ (c_sp1 cx - 4096 <= a < c_sp1 cx) ->
             aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha H1 H2 H3. rewrite (KM a Ha H2 H3). exact (KT a Ha H1). }
assert (P2 : getr regs2 2%bv = getr regsT 2%bv) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3%bv = getr regsT 3%bv) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4%bv = getr regsT 4%bv) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr regsT 8%bv) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9%bv = getr regsT 9%bv) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18%bv = getr regsT 18%bv) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19%bv = getr regsT 19%bv) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20%bv = getr regsT 20%bv) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21%bv = getr regsT 21%bv) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22%bv = getr regsT 22%bv) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23%bv = getr regsT 23%bv) by exact (HP2 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24%bv = getr regsT 24%bv) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
assert (GS : forall off v, 0 <= off <= 176 -> gslot cx W3 ms3 off v ->
             rdword (aview SEGS (w_H W3) mem2) (c_sp1 cx + off) = Some v).
{ intros off v Ho Hv. apply (schc_rdword (w_H W3) (ms_mem ms3) mem2); [|exact Hv].
  intros i Hi. apply KD; lia. }
pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & LWS & LST & _).
apply (HN cx fp k acc ly3 S3 W3 (mkst regs2 (w64 (BASE + GP_sch3)) mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrs Hmo).
exists t.
split; [split|].
- (* the body at 0x81b1c *)
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { split; [cbn [ms_regs mkst]; rewrite P2; exact T2|].
    split; [cbn [ms_regs mkst]; rewrite P8; exact T8|].
    split; [cbn [ms_regs mkst]; rewrite P9; exact T9|].
    split; [cbn [ms_regs mkst]; rewrite P3; exact T3 | cbn [ms_regs mkst]; rewrite P4; exact T4]. }
  split.
  { destruct Hsv as (Hra & Hsj). cbn [ms_mem mkst]. split.
    - apply (schc_rdword (w_H W3) (ms_mem ms3) mem2); [|exact Hra]. intros i Hi. apply KD; lia.
    - intros j Hj. apply (schc_rdword (w_H W3) (ms_mem ms3) mem2); [|exact (Hsj j Hj)]. intros i Hi. apply KD; lia. }
  split.
  { intros i Hi. replace (length GSH_sched) with 104%nat in Hi by reflexivity. cbn [ms_mem mkst].
    rewrite (schc_gsh i Hi).
    destruct ((72 <=? i)%nat && (i <? 90)%nat) eqn:Hw.
    - apply andb_prop in Hw as [Hw1 Hw2]. apply Nat.leb_le in Hw1. apply Nat.ltb_lt in Hw2.
      rewrite KM by lia. apply ZT. lia.
    - assert (Hw' : (i < 72)%nat \/ (90 <= i)%nat).
      { apply andb_false_iff in Hw. destruct Hw as [Hw|Hw]; [left; apply Nat.leb_gt in Hw | right; apply Nat.ltb_ge in Hw]; lia. }
      rewrite KD by lia. apply Hsh. rewrite Hlen. exact Hi. }
  split.
  { cbn [ms_mem mkst]. apply (schc_rdword (w_H W3) (ms_mem ms3) mem2); [|exact Hflg]. intros i Hi. apply KD; lia. }
  split; [reflexivity|].
  { cbn [ms_mem mkst]. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2); [|exact Hinp].
    intros a Ha. rewrite length_map in Ha.
    destruct Hpn as [(Hn0 & _) | (Hn0 & Hin0)]; [unfold c_n in Hn0; lia|].
    assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; left; exact Hin0).
    destruct (HBK _ _ Hin (a - c_p cx) ltac:(unfold c_n in *; lia)) as (B1 & B2 & B3 & B4).
    replace a with (c_p cx + (a - c_p cx)) by lia. apply KD; assumption. }
- (* the rest of what every cut of the phase carries *)
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hblk|]. split; [exact Hn26|].
  split; [cbn [ms_regs mkst]; rewrite P19; exact T19|].
  split; [cbn [ms_regs mkst]; rewrite P22; exact T22|].
  split; [exact (GS 8 _ ltac:(lia) S8)|].
  split; [exact (GS 40 _ ltac:(lia) S40)|].
  split; [exact (GS 48 _ ltac:(lia) S48)|].
  split; [exact (GS 64 _ ltac:(lia) S64)|].
  split; [exact (GS 72 _ ltac:(lia) S72)|].
  split; [exact (GS 96 _ ltac:(lia) S96)|].
  split; [exact (GS 112 _ ltac:(lia) S112)|].
  split; [exact (GS 128 _ ltac:(lia) S128)|].
  split; [exact (GS 136 _ ltac:(lia) S136)|].
  split; [exact (GS 144 _ ltac:(lia) S144)|].
  split; [exact (GS 152 _ ltac:(lia) S152)|].
  split.
  { unfold gfarr in *. cbn [ms_mem mkst]. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2); [|exact Hwas].
    intros a Ha. rewrite length_map, LWS in Ha. apply KD; unfold GO_WAS in *; lia. }
  split.
  { unfold gfarr in *. cbn [ms_mem mkst]. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2); [|exact Hset].
    intros a Ha. rewrite length_map, LST in Ha. apply KD; unfold GO_SET in *; lia. }
  split; [exact Hrel | exact HI1].
- (* the registers, the table and unset_sent *)
  split; [cbn [ms_regs mkst]; rewrite P18; exact T18|].
  split; [cbn [ms_regs mkst]; rewrite P20; exact T20|].
  split; [cbn [ms_regs mkst]; rewrite P21; exact T21|].
  split; [cbn [ms_regs mkst]; rewrite P23; exact T23|].
  split; [cbn [ms_regs mkst]; rewrite P24; exact T24|].
  split.
  { destruct Htab as (Htb & Ht0 & HtL & Htv). split; [exact Htb|]. split; [exact Ht0|]. split; [exact HtL|].
    intros i Hi H438 H439 H451. cbn [ms_mem mkst].
    destruct (HBK _ _ Htb i Hi) as (B1 & B2 & B3 & B4). rewrite KD by assumption. exact (Htv i Hi H438 H439 H451). }
  { unfold gfarr. cbn [ms_mem mkst].
    exact (garr8_of_memset SEGS (w_H W3) mem2 (gF cx fp + 576) 0 144 ltac:(lia) Heff). }
Qed.

(* ---- the segment ---- *)
Theorem sch_segC : forall POST, sch_segC_stmt B MT POST.
Proof.
intros POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HI.
pose proof HI as HI0. unfold GI_sch2 in HI0.
destruct HI0 as (t & HC & R20 & R21 & R24 & R23 & R27 & Htab).
pose proof HC as (Hbody & Hk & Hacc & Hblk & Hn26 & R19 & R22 & S8 & S40 & S48 & S64 & S72 & S96 & S112
                  & S128 & S136 & S144 & S152 & Hwas & Hset & Hrel & HI1).
pose proof HB as (HPRE & _ & _ & Hpn & _ & _ & _ & _ & _ & _ & HE0 & Husp & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (ge_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EFA.
pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (HF0 & HFc & HFia & HFo & HSHeq).
pose proof (ge_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (Hs0 & Hs1).
pose proof (Seg_sched_setup.pos_raw_le (c_pl cx)) as Hpr.
(* the atoms of sch_env this walk reads *)
pose proof (sch_env_E B MT cx fp t (ms_regs ms3) HB) as HE.
pose proof (sch_env_33 cx fp t (ms_regs ms3)) as E33.
assert (E40 : ew (sch_env cx fp t (ms_regs ms3)) 40 = Z_to_bv 64 (sch_b cx 6))
  by exact (sch_env_b cx fp t (ms_regs ms3) 6%nat ltac:(lia)).
assert (E41 : ew (sch_env cx fp t (ms_regs ms3)) 41 = Z_to_bv 64 (sch_b cx 7))
  by exact (sch_env_b cx fp t (ms_regs ms3) 7%nat ltac:(lia)).
assert (E551 : ew (sch_env cx fp t (ms_regs ms3)) 551 = getr (ms_regs ms3) 21)
  by exact (sch_env_reg cx fp t (ms_regs ms3) 21%bv ltac:(vm_compute; discriminate)).
assert (E552 : ew (sch_env cx fp t (ms_regs ms3)) 552 = getr (ms_regs ms3) 22)
  by exact (sch_env_reg cx fp t (ms_regs ms3) 22%bv ltac:(vm_compute; discriminate)).
assert (E553 : ew (sch_env cx fp t (ms_regs ms3)) 553 = getr (ms_regs ms3) 23)
  by exact (sch_env_reg cx fp t (ms_regs ms3) 23%bv ltac:(vm_compute; discriminate)).
assert (E554 : ew (sch_env cx fp t (ms_regs ms3)) 554 = getr (ms_regs ms3) 24)
  by exact (sch_env_reg cx fp t (ms_regs ms3) 24%bv ltac:(vm_compute; discriminate)).
assert (E557 : ew (sch_env cx fp t (ms_regs ms3)) 557 = getr (ms_regs ms3) 27)
  by exact (sch_env_reg cx fp t (ms_regs ms3) 27%bv ltac:(vm_compute; discriminate)).
(* the shadow checks of the frame count's bytes pass: the input's first m bytes from
   SCH_P on lie in the caller's block, whose shadow marks them usable *)
assert (SHOKg : forall m, (1 <= m)%nat -> Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx)) + Z.of_nat m <= c_n cx ->
          sh_ok SEGS sch_Bx (sch_SH m) (sch_env cx fp t (ms_regs ms3)) (mrestrict (w_H W3) (ms_mem ms3))).
{ intros m Hm1 Hmn. destruct m as [|m']; [lia|]. cbn [sch_SH].
  destruct Hpn as [(Hn0 & _) | (Hn0 & Hin0)]; [lia|].
  assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; left; exact Hin0).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin) as (_ & Hp4096 & Hpceil & Hpapp & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
  pose proof HE as (_ & E32' & _). unfold GA_SB in E32'.
  constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) _ sch_Bx 33 (c_p cx) (c_n cx) (SCH_P cx) 0 (Z.of_nat (S m'))).
  - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) (c_p cx) (c_n cx)
             (proj1 HJ) Hin ltac:(lia) ltac:(lia)).
  - unfold U, sch_Bx. rewrite ge_sv_SOff0, E32'. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  - unfold U. rewrite ge_sv_SOff0, E33. apply unsigned_lit_small. unfold SCH_P. lia.
  - unfold SCH_P. lia.
  - unfold SCH_P. lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, SCH_P in *. lia. }
(* three cases on the bytes left for the frame count *)
assert (HLc : sch_L cx <= 6 \/ sch_L cx = 7 \/ 8 <= sch_L cx) by lia.
destruct HLc as [HL | [HL | HL]].
(* none: s7 = 0, both bytes read as 0 *)
1: assert (H27 : getr (ms_regs ms3) 27 = sv_denot (sch_env cx fp t (ms_regs ms3)) (SOff 557 0))
     by (rewrite ge_sv_SOff0; symmetry; exact E557).
1: pose proof (schc_seat cx fp k acc ly3 S3 W3 ms3 md3 0 (SOff 557 0) t HB HJ Hfrs HC ltac:(lia)
                ltac:(unfold c_n; lia) H27) as HS0.
1: pose proof (st_ok_pi_pin_reg' _ _ _ 23%bv 0 HS0
                ltac:(cbn [ms_regs restrict]; rewrite R23; unfold w64; f_equal; lia)
                ltac:(vm_compute; reflexivity)) as HS.
1: assert (SHOK : sh_ok SEGS sch_Bx (sch_SH 0) (sch_env cx fp t (ms_regs ms3)) (mrestrict (w_H W3) (ms_mem ms3)))
     by (cbn [sch_SH]; constructor).
1: assert (B6z : sch_b cx 6 = 0)
     by (unfold sch_b, sbat; apply Seg_sched_setup.bat_out; unfold sch_L, c_n in HL; lia).
1: assert (B7z : sch_b cx 7 = 0)
     by (unfold sch_b, sbat; apply Seg_sched_setup.bat_out; unfold sch_L, c_n in HL; lia).
(* one: s7 = 1, the high byte reads as 0 *)
2: assert (H27 : getr (ms_regs ms3) 27 = sv_denot (sch_env cx fp t (ms_regs ms3)) (SOff 33 6))
     by (rewrite R27 by lia; rewrite (schc_sv_off _ 33 (SCH_P cx) 6 E33); reflexivity).
2: pose proof (schc_seat cx fp k acc ly3 S3 W3 ms3 md3 7 (SOff 33 6) t HB HJ Hfrs HC ltac:(lia)
                ltac:(unfold sch_L in HL; lia) H27) as HS0.
2: pose proof (st_ok_pi_pin_reg' _ _ _ 23%bv 1 HS0
                ltac:(cbn [ms_regs restrict]; rewrite R23; unfold w64; f_equal; lia)
                ltac:(vm_compute; reflexivity)) as HS.
2: pose proof (SHOKg 7%nat ltac:(lia) ltac:(unfold sch_L in HL; lia)) as SHOK.
2: assert (B7z : sch_b cx 7 = 0)
     by (unfold sch_b, sbat; apply Seg_sched_setup.bat_out; unfold sch_L, c_n in HL; lia).
(* two or more: s7 >= 2 *)
3: assert (H27 : getr (ms_regs ms3) 27 = sv_denot (sch_env cx fp t (ms_regs ms3)) (SOff 33 6))
     by (rewrite R27 by lia; rewrite (schc_sv_off _ 33 (SCH_P cx) 6 E33); reflexivity).
3: pose proof (schc_seat cx fp k acc ly3 S3 W3 ms3 md3 8 (SOff 33 6) t HB HJ Hfrs HC ltac:(lia)
                ltac:(unfold sch_L in HL; lia) H27) as HS0.
3: assert (F553 : afact_ok (sch_env cx fp t (ms_regs ms3)) 553 (mkAF 2 (2 ^ 26) 0))
     by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E553, R23;
         unfold w64, sch_L, c_n in *; rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
3: pose proof (st_ok_pi_add_fact _ _ _ 553 _ HS0 F553) as HS.
3: pose proof (SHOKg 8%nat ltac:(lia) ltac:(unfold sch_L in HL; lia)) as SHOK.
(* the walk, the same for the three cases *)
all: clear HS0 HL.
all: remember (sch_env cx fp t (ms_regs ms3)) as E eqn:HEdef.
all: assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
all: clear HEdef.
all: pose proof HE as (AG & E32 & E60 & E516 & E528 & E529).
all: unfold GA_SB, GA_SP1, GA_F, GA_FL, GA_FSH in E32, E60, E516, E528, E529.
all: norm_ss HS.
all: cbn [sch_SH] in SHOK.
(* 0x81a50 .. 0x81ac0: the frame count's bytes, each read after the pointer-overflow
   guard (0x81a5c, 0x81a9c; the trap 0x81f48 is not taken) and the shadow byte of its
   address (the error paths 0x81fb0, 0x81fe8 are not taken) *)
all: paj_run_tok RUN HS HJ SHOK sch_span.
all: lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awr_ok_tac | _ => idtac end.
all: rename HFr into HFrA; clear HF HG.
(* 0x81ac0: the shadow bytes of unset_sent become writable *)
all: lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
       assert (WR : forall o, 72 <= o < 90 -> writable_at SEGS (mrestrict (w_H W3) (ms_mem msx)) (gSH cx fp + o))
         by (destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp (proj1 HJ) (ge_fin fp S3 Hfrs)) as (_ & _ & _ & HFSp);
             intros o Ho; apply (apresent_writable SEGS); rewrite EFA in HFSp;
             replace (gSH cx fp + o) with (shadow_addr (gF cx fp) + o)
               by (unfold shadow_addr; rewrite HSHeq; reflexivity);
             apply (proj1 (HFSp o ltac:(change (fs_frame_bytes GE_CID / 8) with 128; lia))))
     end.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
       let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
       let HS3 := fresh "HS3" in
       pose proof (ast_ok_pi_set_region Ex ssx msx 3 r (set_window r 72 90) HS ltac:(vm_compute; reflexivity) eq_refl
         ltac:(vm_compute; reflexivity)
         (region_ok_rewindow _ Ex _ r 72 90 (st_ok_pi_region_nth Ex ssx msx 3 r HS ltac:(vm_compute; reflexivity))
           ltac:(cbn [YP09.r_base YP09.base_val ms_mem restrict]; rewrite ?ew_ewset_other by lia;
                 rewrite E529; unfold w64; rewrite unsigned_lit_small by lia; exact WR))) as HS3;
       clear HS; rename HS3 into HS; norm_ss HS
     end.
(* 0x81ac0 .. 0x81b18: the shadow stores, s4, the arguments, and the call *)
all: paj_run_shc RUNP RUNC HS HJ.
all: lazymatch goal with
     | |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp0 ?b0 ?bc ?ly ?own =>
       let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp0 b0 bc ly own);
       repeat first
         [ apply awr_ok_nil
         | apply awr_ok_cons_ro; [cbn; lia|]
         | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (gSH cx fp));
           [ reflexivity
           | rewrite ?ew_ewset_other by lia; rewrite E529; unfold w64; apply unsigned_lit_small; lia
           | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists GE_CID, fp;
             split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd]; rewrite EFA;
             unfold shadow_addr; rewrite <- HSHeq; change (fs_frame_bytes GE_CID / 8) with 128; lia
           | ] ]
     | |- _ => idtac
     end.
all: rename HFr into HFrB; clear HF HG.
(* the wrapper __asan_memset and the cut at its return *)
all: lazymatch type of HS with st_ok _ _ _ (restrict _ ?msc) =>
       pmkst HS;
       apply (schc_land POST cx fp k acc ly3 S3 W3 ms3 (ms_regs msc) (ms_mem msc) _ t HB HJ Hfrs Hmo HC Htab)
     end.
all: first
  [ exact HN
  | (* the memory outside unset_sent's shadow is the one at 0x81a50 *)
    lazymatch goal with |- forall a : Z, _ -> ~ _ -> aview _ _ _ a = aview _ _ _ a =>
      let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in intros a Ha Hw;
      lazymatch type of HFrA with frame_of ?E0 ?rs0 _ _ =>
      lazymatch type of HFrB with frame_of ?E1 ?rs1 _ _ =>
        assert (N0 : ~ in_wrange E0 rs0 a)
          by (let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
              intros (rg & Hin & Hrg);
              lazymatch type of Hin with In _ ?l => let l1 := eval vm_compute in l in change (In rg l1) in Hin end;
              cbn [In] in Hin;
              repeat (destruct Hin as [<- | Hin];
                [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hrg; rewrite ?ew_ewset_other in Hrg by lia;
                  rewrite ?E529 in Hrg; unfold w64 in Hrg; rewrite ?unsigned_lit_small in Hrg by lia; lia | ]);
              destruct Hin);
        assert (N1 : ~ in_wrange E1 rs1 a)
          by (let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
              intros (rg & Hin & Hrg);
              lazymatch type of Hin with In _ ?l => let l1 := eval vm_compute in l in change (In rg l1) in Hin end;
              cbn [In] in Hin;
              repeat (destruct Hin as [<- | Hin];
                [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hrg; rewrite ?ew_ewset_other in Hrg by lia;
                  rewrite ?E529 in Hrg; unfold w64 in Hrg; rewrite ?unsigned_lit_small in Hrg by lia; lia | ]);
              destruct Hin);
        rewrite (schc_kept _ _ _ _ _ a HFrB Ha N1); exact (schc_kept _ _ _ _ _ a HFrA Ha N0)
      end end end
  | (* unset_sent's shadow bytes are 0 at the call *)
    lazymatch goal with |- forall i : Z, 72 <= i < 90 -> _ =>
      let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
      lazymatch goal with |- aview _ _ (ms_mem ?msc) _ = _ =>
      lazymatch goal with HSc : st_ok _ ?Ex ?ssx (restrict ?H msc) |- _ =>
        let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
        let R3 := fresh "R3" in
        pose proof (st_ok_region_nth Ex ssx (restrict H msc) 3 r HSc ltac:(vm_compute; reflexivity)) as R3;
        apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msc)); [|lia];
        let j := fresh "j" in let Hj := fresh "Hj" in
        assert (Hj : exists j, (j < 18)%nat /\ i = 72 + Z.of_nat j) by (exists (Z.to_nat (i - 72)); split; lia);
        destruct Hj as (j & Hj & ->);
        apply (field_of_region Ex _ 529%nat (gSH cx fp) _ 0 128 72 90 (72 + Z.of_nat j) 1%N (SLit 0) 0 R3);
        [ rewrite ?ew_ewset_other by lia; rewrite E529; unfold w64; apply unsigned_lit_small; lia
        | do 18 (destruct j as [|j]; [cbn [In]; repeat (first [left; reflexivity | right]) |]); lia
        | reflexivity | cbn; lia | cbn; lia ]
      end end end
  | (* the registers at the call *)
    lazymatch goal with |- getr (ms_regs ?msc) ?r = _ =>
      lazymatch goal with HSc : st_ok _ ?Ex ?ssx (restrict ?H msc) |- _ =>
        rewrite (st_ok_restrict_reg SEGS H Ex ssx msc r HSc);
        let v := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with v
      end end;
    repeat match goal with Hz : sch_b _ _ = 0 |- context [sch_b _ _] => rewrite Hz end;
    rewrite ?Z.mul_0_r, ?Z.add_0_r;
    first
    [ reflexivity
    | lazymatch goal with HX : img_env _ _ ?Ex |- sv_denot ?Ex (SOff 240 ?kk) = _ => exact (codeptr_val Ex kk HX) end
    | rewrite (schc_sv_off _ 516 (gF cx fp) 576) by (rewrite ?ew_ewset_other by lia; exact E516); reflexivity
    | rewrite ge_sv_SOff0, ?ew_ewset_other by lia;
      first [ exact E60 | exact E529
            | rewrite (AG 2%nat ltac:(lia)), (HE0 2%nat 2%bv eq_refl); unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned
            | rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)
            | rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)
            | exact E40
            | rewrite E551; exact R21 | rewrite E552; exact R22 | rewrite E554; exact R24 ]
    | rewrite denot_lit_U, (schc_U_or _ (sch_b cx 6) (sch_b cx 7));
      [ reflexivity | rewrite ?ew_ewset_other by lia; exact E40 | rewrite ?ew_ewset_other by lia; exact E41
      | apply sbat_range | apply sbat_range ]
    | rewrite denot_lit_U, (schc_U_hi _ (sch_b cx 7));
      [ reflexivity | rewrite ?ew_ewset_other by lia; exact E41 | apply sbat_range ]
    | (* s4 = 0 | b6 when only one byte was left *)
      rewrite denot_lit_U, U_SAlu, U_SLit, (U_atom_off _ 40 (sch_b cx 6) 0);
      [ cbn [zalu_raw]; change (zcanon 0) with 0; rewrite Z.lor_0_l, Z.add_0_r;
        rewrite zcanon_id; [reflexivity | unfold M64, sch_b; pose proof (sbat_range (c_pl cx) 6); lia]
      | rewrite ?ew_ewset_other by lia; exact E40
      | unfold sch_b; pose proof (sbat_range (c_pl cx) 6); lia
      | unfold sch_b; pose proof (sbat_range (c_pl cx) 6); lia ] ] ].
Qed.

End c.
End b.
End a.
