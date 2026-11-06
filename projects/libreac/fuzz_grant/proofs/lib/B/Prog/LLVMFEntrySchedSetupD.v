(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedSetupD), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACgb.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedSetupD.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySchedSetupD.v, ported from a working branch 7c8c67da870 (blob 3450d9f151c): image B's own slots 0x81b1c .. 0x81bb0, its register file at the cut (the count in s4, its bytes in s2 and s5, the scene in s7 and s8), its spill slots (the region is s1 + 40 .. s1 + 160 with the write window 80 .. 128, the reads 40, 136 and 152 and the kept slots 96 and 112), and what image B computes that image A does not: the complements of &was_set and &unset_sent into slots 88 and 80 for the frame loop's UBSan pointer guards, the scene's base into slot 120 and base + width (a 64-bit add) into slot 104, the scheduler's flag in s7, the turn counter -(count mod 4097) in s5, and the loop constants 47, 1, -1, -8 and 2 in s2, s9, s10, s8 and s11. *)

(* Segment D of the scheduler's setup in fuzz_grant's entry function LLVMFuzzerTestOneInput
   on the ASan+UBSan build (LLVMFEntrySchedSetupDefs.v): the slots 0x81b1c .. 0x81bb0, from
   the return of __asan_memset to the head of the frame loop (GI_sched, 0x81bb0) or to the
   free of the head-amp table (GI_freeT, 0x81da4).

   The block takes the frame count c (two input bytes, b6 + 256 * b7, which 0x81b00 left in
   s4 with its low byte in s2 and its high byte shifted in s5) modulo 4097, the way the
   compiler writes that division: a multiply-high by 0xfff10000 and a shift by 28 give
   c / 4097, and c - ((c / 4097) << 12 | c / 4097) is c mod 4097. The branch at 0x81b34
   tests zext16(subw(c, b6 << 12)) < 16, which holds exactly when c mod 4097 is 0; both
   facts are checked here by vm_compute over the 65536 pairs of bytes. When the count is 0
   the block goes to the free of the table (s4 reloaded from slot 152 at 0x81b30);
   otherwise it fills the four spill slots the frame loop reads (120 the scene's base, 104
   the scene's end, 88 and 80 the complements of &was_set and &unset_sent, read from slots
   136 and 40), puts the scheduler's flag in s7, -(count mod 4097) in s5 and the loop's
   constants in s2, s8, s9, s10 and s11.

   The block reads the machine frame's slots 40, 136 and 152 and writes 80, 88, 104 and
   120, so the walk's one region is the 120 bytes at s1 + 40 with the write window
   s1 + 80 .. s1 + 128; the slots 96 and 112 lie in that window and are carried as chunks.
   Every other byte this phase's facts speak about lies outside the window and is kept by
   the run's frame_of.

   The block makes no call and reads no shadow byte: the branch at 0x81b34 is its only
   branch, and both of its sides are walked here, so it has no slot into the error path
   (neither the trap at 0x81f48 nor a report of the memory-checking runtime). *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
YC1g YC1h YC1i YC45 YC85 GrantACjr ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySchedSetupDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel GrantSlotPlan SlotNeeds_c HeadampSched SegSetModel Seg_sched_setup.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the values the block computes, as the walk engine builds them ---- *)
(* The atoms are the registers at 0x81b1c: 18 (s2) the frame count's low byte, 20 (s4) the
   count, 21 (s5) its high byte shifted by 8, 23 (s7) and 24 (s8) the scene's base and
   width. *)
(* 0x81b1c .. 0x81b28: zext16(subw(c, b6 << 12)), the left side of the branch. *)
Definition SD_A : sv :=
  SAlu ALU_SRL
    (SAlu ALU_SLL (SAluw ALU_SUB (SOff 20 0) (SAlu ALU_SLL (SOff 18 0) (SLit 12))) (SLit 48))
    (SLit 48).
(* 0x81b64 .. 0x81b8c: c / 4097, by multiply-high and shift. *)
Definition SD_Q : sv :=
  SAlu ALU_SRL
    (SMd M_MULHU
       (SAlu ALU_ADD (SAlu ALU_SLL (SOff 18 0) (SLit 48)) (SAlu ALU_SLL (SOff 21 0) (SLit 48)))
       (SLit 4293984256))
    (SLit 28).
(* 0x81b90 .. 0x81ba8: -(c mod 4097), the turn counter in s5. *)
Definition SD_X21 : sv :=
  SAlu ALU_SUB (SLit 0)
    (SAlu ALU_AND
       (SAlu ALU_SUB (SAlu ALU_ADD (SOff 18 0) (SOff 21 0))
          (SAlu ALU_OR (SAlu ALU_SLL SD_Q (SLit 12)) SD_Q))
       (SLit 65535)).
(* 0x81b44, 0x81b48, 0x81b7c: the scheduler's flag in s7; 0x81b50: the scene's end. *)
Definition SD_F23 : sv :=
  SAlu ALU_AND (SAlu ALU_SLTU (SOff 23 0) (SLit 48)) (SAlu ALU_SLTU (SLit 0) (SOff 24 0)).
Definition SD_S104 : sv := SAlu ALU_ADD (SOff 23 0) (SOff 24 0).

(* The two bytes of the frame count, and the two bytes of the scene, as environments. *)
Definition env_fr (b6 b7 : Z) : env :=
  mkEnv (fun n => if (n =? 18)%nat then Z_to_bv 64 b6
                  else if (n =? 20)%nat then Z_to_bv 64 (b6 + 256 * b7)
                  else if (n =? 21)%nat then Z_to_bv 64 (256 * b7)
                  else Z_to_bv 64 0) (fun _ => []).
Definition env_sb (sb sw : Z) : env :=
  mkEnv (fun n => if (n =? 23)%nat then Z_to_bv 64 sb
                  else if (n =? 24)%nat then Z_to_bv 64 sw
                  else Z_to_bv 64 0) (fun _ => []).

(* ---- the two brute-force facts, over every pair of bytes ---- *)
Lemma sd_brute_fr :
  forallb (fun i => forallb (fun j =>
     let b6 := Z.of_nat i in let b7 := Z.of_nat j in
     (Bool.eqb (bv_unsigned (sv_denot (env_fr b6 b7) SD_A) <? 16) ((b6 + 256 * b7) mod 4097 =? 0)
      && (bv_unsigned (sv_denot (env_fr b6 b7) SD_X21)
          =? bv_unsigned (Z_to_bv 64 (0 - (b6 + 256 * b7) mod 4097))))%bool)
     (seq 0 256)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sd_brute_sb :
  forallb (fun i => forallb (fun j =>
     let sb := Z.of_nat i in let sw := Z.of_nat j in
     ((bv_unsigned (sv_denot (env_sb sb sw) SD_F23)
       =? (if (negb (sw =? 0) && (sb <? 48))%bool then 1 else 0))
      && (bv_unsigned (sv_denot (env_sb sb sw) SD_S104) =? sb + sw))%bool)
     (seq 0 256)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sd_fr_facts : forall b6 b7, 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  (bv_unsigned (sv_denot (env_fr b6 b7) SD_A) <? 16) = ((b6 + 256 * b7) mod 4097 =? 0) /\
  sv_denot (env_fr b6 b7) SD_X21 = Z_to_bv 64 (0 - (b6 + 256 * b7) mod 4097).
Proof.
intros b6 b7 H6 H7. pose proof sd_brute_fr as H. rewrite forallb_forall in H.
specialize (H (Z.to_nat b6) ltac:(apply in_seq; lia)). cbv beta in H.
rewrite forallb_forall in H. specialize (H (Z.to_nat b7) ltac:(apply in_seq; lia)).
cbv beta zeta in H. rewrite !Z2Nat.id in H by lia.
apply andb_prop in H as [H1 H2]. apply Bool.eqb_prop in H1. apply Z.eqb_eq in H2.
split; [exact H1 | apply bv_eq; exact H2].
Qed.

Lemma sd_sb_facts : forall sb sw, 0 <= sb < 256 -> 0 <= sw < 256 ->
  sv_denot (env_sb sb sw) SD_F23
    = Z_to_bv 64 (if (negb (sw =? 0) && (sb <? 48))%bool then 1 else 0) /\
  sv_denot (env_sb sb sw) SD_S104 = Z_to_bv 64 (sb + sw).
Proof.
intros sb sw Hb Hw. pose proof sd_brute_sb as H. rewrite forallb_forall in H.
specialize (H (Z.to_nat sb) ltac:(apply in_seq; lia)). cbv beta in H.
rewrite forallb_forall in H. specialize (H (Z.to_nat sw) ltac:(apply in_seq; lia)).
cbv beta zeta in H. rewrite !Z2Nat.id in H by lia.
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
split; apply bv_eq; [rewrite H1 | rewrite H2]; symmetry; apply unsigned_lit_small;
  [destruct (negb (sw =? 0) && (sb <? 48))%bool |]; lia.
Qed.

(* The same values under any environment that gives those atoms the same words. *)
Lemma sd_denot_fr : forall E b6 b7,
  ew E 18 = Z_to_bv 64 b6 -> ew E 20 = Z_to_bv 64 (b6 + 256 * b7) ->
  ew E 21 = Z_to_bv 64 (256 * b7) ->
  sv_denot E SD_A = sv_denot (env_fr b6 b7) SD_A /\
  sv_denot E SD_X21 = sv_denot (env_fr b6 b7) SD_X21.
Proof.
intros E b6 b7 H18 H20 H21. unfold SD_A, SD_X21, SD_Q, env_fr.
cbn [sv_denot ew Nat.eqb]. rewrite H18, H20, H21. split; reflexivity.
Qed.

Lemma sd_denot_sb : forall E sb sw,
  ew E 23 = Z_to_bv 64 sb -> ew E 24 = Z_to_bv 64 sw ->
  sv_denot E SD_F23 = sv_denot (env_sb sb sw) SD_F23 /\
  sv_denot E SD_S104 = sv_denot (env_sb sb sw) SD_S104.
Proof.
intros E sb sw H23 H24. unfold SD_F23, SD_S104, env_sb.
cbn [sv_denot ew Nat.eqb]. rewrite H23, H24. split; reflexivity.
Qed.

(* The bitwise complement `not` (`xori r,r,-1`) the engine leaves for 0x81b3c and 0x81b5c,
   as the 64-bit number GI_sched states. *)
Lemma sd_not_denot : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros E n x Hn Hx. apply bv_eq. rewrite (unsigned_lit_small (2 ^ 64 - 1 - x)) by lia.
exact (U_not E n x Hn Hx).
Qed.

(* ---- the symbolic state at 0x81b1c ---- *)
(* The atoms are the registers at the cut, and 32 .. 36 the values of the slots the block
   reads or keeps: 32 = &unset_sent (slot 40), 33 = &was_set (slot 136), 34 the table
   (slot 152), 35 = &value (slot 96), 36 = &par (slot 112). *)
Definition SD_Bx : sv := SLit SCH_SB.
Definition SD_span : Z * Z := sch_span.
Definition R_sd : YP09.region :=
  YP09.mkRegion (Some 9%nat) 40 160 80 128
    [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 96 (CVal 8 (SOff 35 0));
     YP09.mkChunk 112 (CVal 8 (SOff 36 0)); YP09.mkChunk 136 (CVal 8 (SOff 33 0));
     YP09.mkChunk 152 (CVal 8 (SOff 34 0))].
Definition G_sd : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition ss_sd : sstate := mkSS GP_sch3 sr_atoms [R_sd] None G_sd.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

(* The machine fields a seated state fixes. *)
Lemma sd_mach : forall E ss (H : word -> bool) (ms : machine_state),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> ss_resv ss = None ->
  ms_pc_val ms = w64 (BASE + ss_pc ss) /\ ms_resv ms = None /\ ms_svc_pending ms = None /\
  ms_rom ms = seg_rom SEGS /\ ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr.
Proof.
intros E ss H ms HS Hrv. unfold st_ok_pi, st_ok in HS.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & _).
cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom] in *.
unfold abs_ss, setpc in H2, H4. cbn in H2, H4. rewrite Hrv in H4. cbn in H4.
unfold w64. repeat split; assumption.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- what the run leaves of the memory ---- *)
(* Every byte outside the write window s1 + 80 .. s1 + 128 is as the block found it. *)
Definition sd_keepP (cx : ecx) (W3 : world SEGS) (ms ms' : machine_state) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 80 <= a < c_sp1 cx + 128) ->
    aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a.

Lemma sd_keep_one : forall cx E (W3 : world SEGS) (m m' : word -> option byte) (cs : list YP09.chunk),
  frame_of E [YP09.mkRegion (Some 9%nat) 40 160 80 128 cs]
    (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  bv_unsigned (ew E 9) = c_sp1 cx ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 80 <= a < c_sp1 cx + 128) ->
    aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
intros cx E W3 m m' cs HF H9 a Ha Hn. apply aview_eq_of. apply HF.
rewrite unsigned_lit_small by lia. intros (r & [<- | []] & Hr).
cbn [YP09.base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. rewrite H9 in Hr. lia.
Qed.

Lemma sd_keep_trans : forall cx W3 ms1 ms2 ms3,
  sd_keepP cx W3 ms1 ms2 -> sd_keepP cx W3 ms2 ms3 -> sd_keepP cx W3 ms1 ms3.
Proof. intros cx W3 ms1 ms2 ms3 H1 H2 a Ha Hn. rewrite (H2 a Ha Hn). exact (H1 a Ha Hn). Qed.

(* ---- where things are: everything this phase speaks of is below the machine frame ---- *)
Lemma sd_geo : forall cx fp W3 (ms : machine_state) ly3 S3 md3 k t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t ->
  spZ (c_regs cx) - 319 <= c_sp1 cx <= spZ (c_regs cx) - 288 /\
  alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\
  0 <= gSH cx fp /\ gSH cx fp + 128 <= alloc_ceiling /\
  4096 <= t /\ t + 460 <= alloc_ceiling /\
  (c_n cx = 0 \/ (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)).
Proof.
intros cx fp W3 ms ly3 S3 md3 k t HB HJ HFR HBL.
pose proof (ge_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
pose proof (ge_F_facts B MT LAWS cx fp W3 ms ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HSHeq).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _).
assert (Hint : In (t, 460) (ablocks B ly3 S3))
  by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hint) as (_ & Ht4096 & Htceil & _).
change (req_size 460) with 460 in Htceil.
assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
assert (Hd1 : gF cx fp / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (Hd2 : alloc_ceiling / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
split; [exact Hsp1|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [exact HF0|]. split; [exact HFc|].
split; [rewrite HSHeq; unfold SHADOW_OFF; lia|].
split; [rewrite HSHeq; unfold SHADOW_OFF; lia|].
split; [exact Ht4096|]. split; [exact Htceil|].
pose proof HB as (_ & _ & _ & Hpn & _).
destruct Hpn as [[Hn0 _] | [Hn Hin0]]; [left; exact Hn0|].
assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
  by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; left; exact Hin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos' (c_n cx) ltac:(lia)) as [_ Hrq]. right. split; lia.
Qed.

(* Every fact of this phase that lives outside the window carries over the run. *)
Lemma sd_mem : forall cx fp W3 (ms ms' : machine_state) ly3 S3 md3 k t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t ->
  sd_keepP cx W3 ms ms' ->
  (gsaved cx W3 ms -> gsaved cx W3 ms') /\
  (forall sh, length sh = GE_NSH -> gshadow cx fp W3 ms sh -> gshadow cx fp W3 ms' sh) /\
  (rdword (aview SEGS (w_H W3) (ms_mem ms)) (gF cx fp + 1016) = Some (gFL cx fp) ->
   rdword (aview SEGS (w_H W3) (ms_mem ms')) (gF cx fp + 1016) = Some (gFL cx fp)) /\
  (garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
   garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx))) /\
  (forall T, gtab B cx ly3 S3 W3 ms t T -> gtab B cx ly3 S3 W3 ms' t T) /\
  (forall off l, 0 <= off -> off + Z.of_nat (length l) <= 1024 ->
     gfarr cx fp W3 ms off l -> gfarr cx fp W3 ms' off l) /\
  (forall o v, 0 <= o -> (o + 8 <= 80 \/ 128 <= o) -> o <= 152 ->
     gslot cx W3 ms o v -> gslot cx W3 ms' o v).
Proof.
intros cx fp W3 ms ms' ly3 S3 md3 k t HB HJ HFR HBL HK.
pose proof (sd_geo cx fp W3 ms ly3 S3 md3 k t HB HJ HFR HBL)
  as (Hsp1 & Hlo & Hhi & HF0 & HFc & HS0 & HS1 & Ht0 & Htc & Hp).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (AV : forall a, 0 <= a -> (a < c_sp1 cx + 80 \/ c_sp1 cx + 128 <= a < 2 ^ 64) ->
   aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a)
  by (intros a Ha Hc; apply HK; lia).
assert (RD : forall a v, 0 <= a ->
   (a + 8 <= c_sp1 cx + 80 \/ (c_sp1 cx + 128 <= a /\ a + 8 <= 2 ^ 64)) ->
   rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v ->
   rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v).
{ intros a v Ha Hc Hr. unfold rdword in Hr |- *.
  rewrite <- (Z.add_0_r a) at 1.
  rewrite (AV (a + 0)), (AV (a + 1)), (AV (a + 2)), (AV (a + 3)),
          (AV (a + 4)), (AV (a + 5)), (AV (a + 6)), (AV (a + 7)) by lia.
  rewrite Z.add_0_r. exact Hr. }
split.
{ intros (Hra & Hsj). split; [apply RD; [lia | lia | exact Hra]|].
  intros j Hj. apply RD; [lia | lia | exact (Hsj j Hj)]. }
split.
{ intros sh Hlen Hsh i Hi. pose proof Hi as Hi2. rewrite Hlen in Hi2. unfold GE_NSH in Hi2.
  rewrite AV by lia. exact (Hsh i Hi). }
split; [intros Hfl; apply RD; [lia | lia | exact Hfl]|].
split.
{ intros Hin. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') _ _); [|exact Hin].
  intros a Ha. rewrite length_map in Ha. unfold c_n in Hp. apply AV; lia. }
split.
{ intros T (Hb & Htt & Hl & Hbytes). split; [exact Hb|]. split; [exact Htt|]. split; [exact Hl|].
  intros i Hi H1 H2 H3. rewrite AV by lia. exact (Hbytes i Hi H1 H2 H3). }
split.
{ intros off l Ho Hl Hg. unfold gfarr in Hg |- *.
  apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') _ _); [|exact Hg].
  intros a Ha. rewrite length_map in Ha. apply AV; lia. }
intros o v Ho Hw Hm Hs. unfold gslot in Hs |- *. apply RD; [lia | lia | exact Hs].
Qed.

(* ---- the two landings ---- *)
Lemma sd_fin_freeT : forall cx fp k acc ly3 S3 W3 (ms ms' : machine_state) md3 md' t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  frames S3 = [(GE_CID, fp)] ->
  sch_common B MT cx fp GP_sch3 GSH_sched k acc ly3 S3 W3 ms t ->
  sd_keepP cx W3 ms ms' ->
  ms_pc_val ms' = w64 (BASE + GP_freeT) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  getr (ms_regs ms') 2 = getr (ms_regs ms) 2 -> getr (ms_regs ms') 8 = getr (ms_regs ms) 8 ->
  getr (ms_regs ms') 9 = getr (ms_regs ms) 9 -> getr (ms_regs ms') 3 = getr (ms_regs ms) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms) 4 -> getr (ms_regs ms') 19 = getr (ms_regs ms) 19 ->
  getr (ms_regs ms') 20 = w64 t ->
  GI_freeT B MT cx fp k acc ly3 S3 W3 ms' md'.
Proof.
intros cx fp k acc ly3 S3 W3 ms ms' md3 md' t HB HJ HFR HC HK
  Hpc Hrv Hsv Hro Hfr Hfc K2 K8 K9 K3 K4 K19 R20.
pose proof HC as (Hbody & Hk & Hacc & Hbl & Hn26 & R19 & R22 & L8 & L40 & L48 & L64 & L72
                  & L96 & L112 & L128 & L136 & L144 & L152 & Hws & Hst & Hrel & HI1).
pose proof Hbody as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & Hsaved & Hsh & Hfl & Hlen & Hinp).
destruct (sd_mem cx fp W3 ms ms' ly3 S3 md3 k t HB HJ HFR Hbl HK)
  as (TSV & TSH & TFL & TIN & TTAB & TARR & TSLOT).
exists t. unfold ge_body, gregs.
split.
{ split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsv|]. split; [exact Hro|].
  split; [exact Hfr|]. split; [exact Hfc|].
  split; [repeat split; congruence|].
  split; [exact (TSV Hsaved)|]. split; [exact (TSH _ Hlen Hsh)|].
  split; [exact (TFL Hfl)|]. split; [exact Hlen | exact (TIN Hinp)]. }
split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hbl|]. split; [exact Hn26|].
split; [exact R20|]. split; [congruence|].
split; apply TSLOT; first [lia | assumption].
Qed.

Lemma sd_fin_sched : forall cx fp k acc ly3 S3 W3 (ms ms' : machine_state) md3 md' t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  frames S3 = [(GE_CID, fp)] ->
  sch_common B MT cx fp GP_sch3 GSH_sched k acc ly3 S3 W3 ms t ->
  gtab B cx ly3 S3 W3 ms t (GrantSlotPlan.T_sched0 (c_pl cx)) ->
  gfarr cx fp W3 ms GO_UNSET GrantSlotPlan.Z144 ->
  sd_keepP cx W3 ms ms' ->
  0 < GrantSlotPlan.frames (c_pl cx) ->
  ms_pc_val ms' = w64 (BASE + GP_sched) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  getr (ms_regs ms') 2 = getr (ms_regs ms) 2 -> getr (ms_regs ms') 8 = getr (ms_regs ms) 8 ->
  getr (ms_regs ms') 9 = getr (ms_regs ms) 9 -> getr (ms_regs ms') 3 = getr (ms_regs ms) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms) 4 -> getr (ms_regs ms') 19 = getr (ms_regs ms) 19 ->
  getr (ms_regs ms') 22 = getr (ms_regs ms) 22 ->
  getr (ms_regs ms') 20 = w64 t ->
  getr (ms_regs ms') 21 = w64 (0 - GrantSlotPlan.frames (c_pl cx)) ->
  getr (ms_regs ms') 23 = w64 (GrantSlotPlan.sched_flag (c_pl cx)) ->
  getr (ms_regs ms') 18 = w64 47 -> getr (ms_regs ms') 24 = w64 (-8) ->
  getr (ms_regs ms') 25 = w64 1 -> getr (ms_regs ms') 26 = w64 (-1) ->
  getr (ms_regs ms') 27 = w64 2 ->
  gslot cx W3 ms' 120 (sch_b cx 0) -> gslot cx W3 ms' 104 (sch_b cx 0 + sch_b cx 1) ->
  gslot cx W3 ms' 80 (2 ^ 64 - 1 - (gF cx fp + GO_UNSET)) ->
  gslot cx W3 ms' 88 (2 ^ 64 - 1 - (gF cx fp + GO_WAS)) ->
  gslot cx W3 ms' 96 (gF cx fp + GO_VAL) -> gslot cx W3 ms' 112 (gF cx fp + GO_PAR) ->
  GI_sched B MT cx fp k acc ly3 S3 W3 ms' md'.
Proof.
intros cx fp k acc ly3 S3 W3 ms ms' md3 md' t HB HJ HFR HC Htab Hun HK Hfr0
  Hpc Hrv Hsv Hro Hfrg Hfc K2 K8 K9 K3 K4 K19 K22 R20 R21 R23 R18 R24 R25 R26 R27
  S120 S104 S80 S88 S96 S112.
pose proof HC as (Hbody & Hk & Hacc & Hbl & Hn26 & R19 & R22 & L8 & L40 & L48 & L64 & L72
                  & L96 & L112 & L128 & L136 & L144 & L152 & Hws & Hst & Hrel & HI1).
pose proof Hbody as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & Hsaved & Hsh & Hfl & Hlen & Hinp).
destruct (sd_mem cx fp W3 ms ms' ly3 S3 md3 k t HB HJ HFR Hbl HK)
  as (TSV & TSH & TFL & TIN & TTAB & TARR & TSLOT).
pose proof (Seg_sched_setup.sched_rd_bat (c_pl cx)) as HSR.
pose proof (HeadampSched.sched0_ok (c_pl cx)) as (HI1s & HLs).
pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & LW & LS & _ & _).
exists 0%nat, t. unfold ge_body, gregs.
split.
{ split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsv|]. split; [exact Hro|].
  split; [exact Hfrg|]. split; [exact Hfc|].
  split; [repeat split; congruence|].
  split; [exact (TSV Hsaved)|]. split; [exact (TSH _ Hlen Hsh)|].
  split; [exact (TFL Hfl)|]. split; [exact Hlen | exact (TIN Hinp)]. }
split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hbl|]. split; [exact Hn26|].
split; [cbn [Z.of_nat]; lia|].
split; [rewrite R21; f_equal; cbn [Z.of_nat]; lia|].
split; [congruence|]. split; [exact R20|]. split; [congruence|].
split; [exact R23|]. split; [exact R18|]. split; [exact R24|].
split; [exact R25|]. split; [exact R26|]. split; [exact R27|].
split.
{ unfold sch_b, sbat in S120, S104. rewrite !Nat.add_0_r in S120, S104.
  destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] f] p4].
  destruct HSR as (Esb & Esw & _ & _).
  rewrite <- Esb in S120. rewrite <- Esb, <- Esw in S104.
  split; [exact S120 | exact S104]. }
do 12 (split; [ first [ exact S80 | exact S88 | exact S96 | exact S112
                      | apply TSLOT; first [lia | assumption] ] |]).
change (GrantSlotPlan.sched_at (c_pl cx) t 0)
  with (GrantSlotPlan.T_sched0 (c_pl cx), GrantSlotPlan.Z144).
cbv iota beta.
split.
{ split; [exact (TTAB _ Htab)|]. split; [exact HI1s|].
  split; [vm_compute; reflexivity|].
  apply (TARR GO_UNSET GrantSlotPlan.Z144); [unfold GO_UNSET; lia | | exact Hun].
  unfold GO_UNSET. replace (length GrantSlotPlan.Z144) with 144%nat by (vm_compute; reflexivity). lia. }
split;
  [ apply (TARR GO_WAS _); [unfold GO_WAS; lia | unfold GO_WAS; rewrite LW; lia | exact Hws] |].
split;
  [ apply (TARR GO_SET _); [unfold GO_SET; lia | unfold GO_SET; rewrite LS; lia | exact Hst]
  | exact Hrel].
Qed.

(* ---- the walk ---- *)
(* The one region is the machine frame's slots 40 .. 159 with the write window 80 .. 127,
   which the journal's stack window covers; nothing else is written. *)
Ltac sd_awr E9 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc ly own) end;
  lazymatch goal with |- awr_ok _ _ _ ?sp0 _ _ _ _ _ =>
    lazymatch goal with Hs : sp0 - 319 <= ?sp1 <= sp0 - 288 |- _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
      [ reflexivity
      | cbn [extK ew]; rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; lia
      | cbn; unfold GE_STK, GrantBContracts.STK_LLVMFuzzerTestOneInput; lia
      | cbn; lia
      | apply awr_ok_nil ] end end.

Ltac sd_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* A register the run left as it found it. *)
Ltac sd_keptr HSx Ex EAx n r :=
  transitivity (sv_denot Ex (SOff n 0));
  [ exact (st_ok_pi_restrict_reg _ Ex _ _ r HSx)
  | rewrite ge_sv_SOff0; exact (EAx n r ltac:(lia) eq_refl) ].

Theorem sch_segD : forall POST, sch_segD_stmt B MT POST.
Proof.
intros POST HN HF cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HI.
destruct HI as (t & HC & R18 & R20 & R21 & R23 & R24 & Htab & Hun).
pose proof HC as (Hbody & Hk & Hacc & Hblk & Hn26 & R19 & R22 & L8 & L40 & L48 & L64 & L72
                  & L96 & L112 & L128 & L136 & L144 & L152 & Hws & Hst & Hrel & HI1).
pose proof Hbody as (Hpc & Hrv & Hsv & Hro & Hfrg & Hfc & Hgr & Hsaved & Hsh & Hfl & Hlen & Hinp).
pose proof Hgr as (G2 & G8 & G9 & G3 & G4).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HJ as HJ0.
pose proof (sd_geo cx fp W3 ms3 ly3 S3 md3 k t HB HJ Hfrs Hblk)
  as (Hsp1 & Hlo & Hhi & HF0 & HFc & HSH0 & HSH1 & Ht0 & Htc & Hpn).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hsp1m : c_sp1 cx mod 32 = 0).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1d & _).
  rewrite Hs1d, Z.mul_comm. apply Z_mod_mult. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* the model: the two bytes of the frame count and the two bytes of the scene *)
pose proof (sbat_range (c_pl cx) 0) as B0. pose proof (sbat_range (c_pl cx) 1) as B1.
pose proof (sbat_range (c_pl cx) 6) as B6. pose proof (sbat_range (c_pl cx) 7) as B7.
unfold sch_b in R18, R20, R21, R23, R24.
pose proof (Seg_sched_setup.sched_rd_bat (c_pl cx)) as HSR.
assert (HFRM : GrantSlotPlan.frames (c_pl cx)
               = (sbat (c_pl cx) 6 + 256 * sbat (c_pl cx) 7) mod 4097).
{ unfold GrantSlotPlan.frames, sbat.
  destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] f] p4].
  destruct HSR as (_ & _ & _ & Ef). exact Ef. }
assert (HFLG : GrantSlotPlan.sched_flag (c_pl cx)
               = (if (negb (sbat (c_pl cx) 1 =? 0) && (sbat (c_pl cx) 0 <? 48))%bool then 1 else 0)).
{ unfold GrantSlotPlan.sched_flag, sbat.
  destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] f] p4].
  destruct HSR as (Esb & Esw & _ & _). rewrite !Nat.add_0_r. rewrite Esb, Esw. reflexivity. }
pose proof (Z.mod_pos_bound (sbat (c_pl cx) 6 + 256 * sbat (c_pl cx) 7) 4097 ltac:(lia)) as HMD.
(* the machine state as the engine wants it *)
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_sch3)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hrv Hsv Hro Hfrg Hfc. destruct ms3. cbn in *. unfold mkst.
  rewrite Hpc, Hrv, Hsv, Hro, Hfrg, Hfc. reflexivity. }
rewrite Hms.
remember (Eimg (Ereg (ms_regs ms3)
  [w64 (gF cx fp + GO_UNSET); w64 (gF cx fp + GO_WAS); w64 t;
   w64 (gF cx fp + GO_VAL); w64 (gF cx fp + GO_PAR)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
             ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_nat _ _ n r Hr)).
assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EA 9%nat 9%bv ltac:(lia) eq_refl); exact G9).
assert (E9u : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 (gF cx fp + GO_UNSET))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = w64 (gF cx fp + GO_WAS))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = w64 t)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (E35 : ew E 35 = w64 (gF cx fp + GO_VAL))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (E36 : ew E 36 = w64 (gF cx fp + GO_PAR))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
assert (E18 : ew E 18 = Z_to_bv 64 (sbat (c_pl cx) 6))
  by (rewrite (EA 18%nat 18%bv ltac:(lia) eq_refl); exact R18).
assert (E20 : ew E 20 = Z_to_bv 64 (sbat (c_pl cx) 6 + 256 * sbat (c_pl cx) 7))
  by (rewrite (EA 20%nat 20%bv ltac:(lia) eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 (256 * sbat (c_pl cx) 7))
  by (rewrite (EA 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
assert (E23 : ew E 23 = Z_to_bv 64 (sbat (c_pl cx) 0))
  by (rewrite (EA 23%nat 23%bv ltac:(lia) eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 (sbat (c_pl cx) 1))
  by (rewrite (EA 24%nat 24%bv ltac:(lia) eq_refl); exact R24).
destruct (sd_denot_fr E _ _ E18 E20 E21) as (DA & DX21).
destruct (sd_fr_facts (sbat (c_pl cx) 6) (sbat (c_pl cx) 7) ltac:(lia) ltac:(lia)) as (FA & FX21).
destruct (sd_denot_sb E _ _ E23 E24) as (DF & DS).
destruct (sd_sb_facts (sbat (c_pl cx) 0) (sbat (c_pl cx) 1) ltac:(lia) ltac:(lia)) as (FF & FS).
(* the seat *)
assert (HS : st_ok_pi SEGS VAL E ss_sd
               (restrict (w_H W3)
                  (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_sch3)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_sd. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold YP09.region_ok, R_sd.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite E9u. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply HJpres.
      unfold GE_STK, GrantBContracts.STK_LLVMFuzzerTestOneInput. lia. }
    unfold GO_UNSET, GO_WAS, GO_VAL, GO_PAR in *.
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ (c_sp1 cx) 40 8 (SOff 32 0) (gF cx fp + 576));
        [rewrite ge_sv_SOff0, E32; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ L40).
    + apply (chunk_ok_val SEGS E _ (c_sp1 cx) 96 8 (SOff 35 0) (gF cx fp + 816));
        [rewrite ge_sv_SOff0, E35; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ L96).
    + apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 36 0) (gF cx fp + 800));
        [rewrite ge_sv_SOff0, E36; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ L112).
    + apply (chunk_ok_val SEGS E _ (c_sp1 cx) 136 8 (SOff 33 0) (gF cx fp + 32));
        [rewrite ge_sv_SOff0, E33; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ L136).
    + apply (chunk_ok_val SEGS E _ (c_sp1 cx) 152 8 (SOff 34 0) t);
        [rewrite ge_sv_SOff0, E34; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ L152).
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. repeat split.
  - split; [|split; exact I]. unfold G_sd. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E9u.
    change (2 ^ 5) with 32. rewrite Hsp1m. lia. }
assert (SHOK : sh_ok SEGS SD_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
(* 0x81b1c .. 0x81b34: up to the branch on the count *)
paj_run_tok RUN HS HJ SHOK SD_span; [sd_awr E9 |].
lazymatch goal with
| HF1 : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (KP1 : sd_keepP cx W3 ms3 m1)
    by (intros a Ha Hn; exact (sd_keep_one cx E W3 (ms_mem ms3) (ms_mem m1) _ HF1 E9u a Ha Hn))
end.
psrr_branch_tok RUN BR HS SHOK SD_span.
- (* the count is 0: the block goes to the free of the table at 0x81da4 *)
  rewrite branch_ltu_U, (U_lit E 16 ltac:(lia)) in Hc.
  assert (Hc0 : ((sbat (c_pl cx) 6 + 256 * sbat (c_pl cx) 7) mod 4097 =? 0) = true)
    by (rewrite <- FA, <- DA; exact Hc).
  apply Z.eqb_eq in Hc0. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK SD_span 0x1368; [sd_awr E9 |].
  lazymatch goal with
  | HF2 : frame_of _ _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)) |- _ =>
    assert (KP2 : sd_keepP cx W3 ms3 m2)
      by (apply (sd_keep_trans cx W3 ms3 m1 m2 KP1); intros a Ha Hn;
          exact (sd_keep_one cx E W3 (ms_mem m1) (ms_mem m2) _ HF2 E9u a Ha Hn))
  end.
  destruct (sd_mach E _ (w_H W3) _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc).
  cbn [ss_pc] in Pc.
  lazymatch goal with
  | HS2 : st_ok_pi _ _ _ _ (restrict _ ?m2) |- SRr _ _ (mkCfg ?m2 ?mdx) _ =>
    apply (HF cx fp k acc ly3 S3 W3 m2 mdx HB HJ Hfrs Hmo);
    apply (sd_fin_freeT cx fp k acc ly3 S3 W3 ms3 m2 md3 mdx t HB HJ0 Hfrs HC KP2)
  end.
  + exact Pc.
  + exact Prv.
  + exact Psv.
  + exact Pro.
  + exact Pfr.
  + exact Pfc.
  + sd_keptr HS E EA 2%nat (2%bv : bv 5).
  + sd_keptr HS E EA 8%nat (8%bv : bv 5).
  + sd_keptr HS E EA 9%nat (9%bv : bv 5).
  + sd_keptr HS E EA 3%nat (3%bv : bv 5).
  + sd_keptr HS E EA 4%nat (4%bv : bv 5).
  + sd_keptr HS E EA 19%nat (19%bv : bv 5).
  + transitivity (sv_denot E (SOff 34 0));
      [ exact (st_ok_pi_restrict_reg _ E _ _ (20%bv : bv 5) HS)
      | rewrite ge_sv_SOff0; exact E34 ].
- (* the count is not 0: the block enters the frame loop at 0x81bb0 *)
  rewrite branch_ltu_U, (U_lit E 16 ltac:(lia)) in Hc.
  assert (Hc0 : ((sbat (c_pl cx) 6 + 256 * sbat (c_pl cx) 7) mod 4097 =? 0) = false)
    by (rewrite <- FA, <- DA; exact Hc).
  apply Z.eqb_neq in Hc0. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK SD_span 0x1174; [sd_awr E9 |].
  lazymatch goal with
  | HF2 : frame_of _ _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)) |- _ =>
    assert (KP2 : sd_keepP cx W3 ms3 m2)
      by (apply (sd_keep_trans cx W3 ms3 m1 m2 KP1); intros a Ha Hn;
          exact (sd_keep_one cx E W3 (ms_mem m1) (ms_mem m2) _ HF2 E9u a Ha Hn))
  end.
  pose proof (st_ok_pi_region_nth E _ _ 0%nat _ HS eq_refl) as HR.
  cbn [ms_mem restrict] in HR.
  destruct (sd_mach E _ (w_H W3) _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc).
  cbn [ss_pc] in Pc.
  lazymatch goal with
  | HS2 : st_ok_pi _ _ _ _ (restrict _ ?m2) |- SRr _ _ (mkCfg ?m2 ?mdx) _ =>
    apply (HN cx fp k acc ly3 S3 W3 m2 mdx HB HJ Hfrs Hmo);
    apply (sd_fin_sched cx fp k acc ly3 S3 W3 ms3 m2 md3 mdx t HB HJ0 Hfrs HC Htab Hun KP2)
  end.
  + rewrite HFRM. lia.
  + exact Pc.
  + exact Prv.
  + exact Psv.
  + exact Pro.
  + exact Pfr.
  + exact Pfc.
  + sd_keptr HS E EA 2%nat (2%bv : bv 5).
  + sd_keptr HS E EA 8%nat (8%bv : bv 5).
  + sd_keptr HS E EA 9%nat (9%bv : bv 5).
  + sd_keptr HS E EA 3%nat (3%bv : bv 5).
  + sd_keptr HS E EA 4%nat (4%bv : bv 5).
  + sd_keptr HS E EA 19%nat (19%bv : bv 5).
  + sd_keptr HS E EA 22%nat (22%bv : bv 5).
  + transitivity (sv_denot E (SOff 34 0));
      [ exact (st_ok_pi_restrict_reg _ E _ _ (20%bv : bv 5) HS)
      | rewrite ge_sv_SOff0; exact E34 ].
  + transitivity (sv_denot E SD_X21);
      [ exact (st_ok_pi_restrict_reg _ E _ _ (21%bv : bv 5) HS)
      | rewrite DX21, FX21, HFRM; reflexivity ].
  + transitivity (sv_denot E SD_F23);
      [ exact (st_ok_pi_restrict_reg _ E _ _ (23%bv : bv 5) HS)
      | rewrite DF, FF, HFLG; reflexivity ].
  + transitivity (sv_denot E (SLit 47));
      [ exact (st_ok_pi_restrict_reg _ E _ _ (18%bv : bv 5) HS) | reflexivity ].
  + transitivity (sv_denot E (SLit 18446744073709551608));
      [ exact (st_ok_pi_restrict_reg _ E _ _ (24%bv : bv 5) HS)
      | cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity ].
  + transitivity (sv_denot E (SLit 1));
      [ exact (st_ok_pi_restrict_reg _ E _ _ (25%bv : bv 5) HS) | reflexivity ].
  + transitivity (sv_denot E (SLit 18446744073709551615));
      [ exact (st_ok_pi_restrict_reg _ E _ _ (26%bv : bv 5) HS)
      | cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity ].
  + transitivity (sv_denot E (SLit 2));
      [ exact (st_ok_pi_restrict_reg _ E _ _ (27%bv : bv 5) HS) | reflexivity ].
  + unfold gslot, sch_b.
    apply (rdword_of_val_mem SEGS (w_H W3) _); [|lia].
    exact (field_of_regionG E _ 9%nat (c_sp1 cx) _ 40 160 80 128 120 8 (SOff 23 0)
             (sbat (c_pl cx) 0) HR E9u ltac:(sd_in)
             ltac:(rewrite ge_sv_SOff0, E23; reflexivity)
             ltac:(cbn; lia) ltac:(cbn; lia)).
  + unfold gslot, sch_b.
    apply (rdword_of_val_mem SEGS (w_H W3) _); [|lia].
    exact (field_of_regionG E _ 9%nat (c_sp1 cx) _ 40 160 80 128 104 8 SD_S104
             (sbat (c_pl cx) 0 + sbat (c_pl cx) 1) HR E9u ltac:(sd_in)
             ltac:(rewrite DS, FS; reflexivity)
             ltac:(cbn; lia) ltac:(cbn; lia)).
  + unfold gslot.
    apply (rdword_of_val_mem SEGS (w_H W3) _); [|unfold GO_UNSET; lia].
    exact (field_of_regionG E _ 9%nat (c_sp1 cx) _ 40 160 80 128 80 8
             (SAlu ALU_XOR (SOff 32 0) (SLit (-1)))
             (2 ^ 64 - 1 - (gF cx fp + GO_UNSET)) HR E9u ltac:(sd_in)
             ltac:(apply (sd_not_denot E 32 _ E32); unfold GO_UNSET; lia)
             ltac:(cbn; unfold GO_UNSET; lia) ltac:(cbn; lia)).
  + unfold gslot.
    apply (rdword_of_val_mem SEGS (w_H W3) _); [|unfold GO_WAS; lia].
    exact (field_of_regionG E _ 9%nat (c_sp1 cx) _ 40 160 80 128 88 8
             (SAlu ALU_XOR (SOff 33 0) (SLit (-1)))
             (2 ^ 64 - 1 - (gF cx fp + GO_WAS)) HR E9u ltac:(sd_in)
             ltac:(apply (sd_not_denot E 33 _ E33); unfold GO_WAS; lia)
             ltac:(cbn; unfold GO_WAS; lia) ltac:(cbn; lia)).
  + unfold gslot.
    apply (rdword_of_val_mem SEGS (w_H W3) _); [|unfold GO_VAL; lia].
    exact (field_of_regionG E _ 9%nat (c_sp1 cx) _ 40 160 80 128 96 8 (SOff 35 0)
             (gF cx fp + GO_VAL) HR E9u ltac:(sd_in)
             ltac:(rewrite ge_sv_SOff0, E35; reflexivity)
             ltac:(cbn; unfold GO_VAL; lia) ltac:(cbn; lia)).
  + unfold gslot.
    apply (rdword_of_val_mem SEGS (w_H W3) _); [|unfold GO_PAR; lia].
    exact (field_of_regionG E _ 9%nat (c_sp1 cx) _ 40 160 80 128 112 8 (SOff 36 0)
             (gF cx fp + GO_PAR) HR E9u ltac:(sd_in)
             ltac:(rewrite ge_sv_SOff0, E36; reflexivity)
             ltac:(cbn; unfold GO_PAR; lia) ltac:(cbn; lia)).
Qed.

End c.
End b.
End a.
