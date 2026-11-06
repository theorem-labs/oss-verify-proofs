(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 962 of its 1056 lines of code are new or changed and 837 lines of the source are left out. *)
(* Case 1 of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput: the segments from C1_P5 (0x807dc) and C1_P6 (0x80984)
   of BoxBLxCase1Defs.v. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBRangeFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase1Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg reac_boxreg_add_c range_free_c lowest_free_c LLVMFuzzerTestOneInput_case1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The engine's shadow base: no shadow check runs in these segments. *)
Definition CW_SB : Z := 0x7fff8000.
Definition CW_BX : sv := SLit CW_SB.
Definition CW_BSPAN : Z * Z := (CW_SB, CW_SB + 2 ^ 44 - 1).

(* The want segment's own atoms (BoxBLxSeat.v lx_env: 48 up): 48 nch, 49 fab, 50 n_before, 51 nonzero. *)
Definition CW_SLOTS : list (Z * sv) :=
  [(0x30, SOff 49 0); (0x48, SOff 50 0); (0x50, SOff 48 0); (0x60, SOff 51 0)].
Definition CW_REG : YP09.region := YP09.mkRegion (Some 9%nat) 0x30 0x68 0 0 (lx_slot_chunks CW_SLOTS).
Definition cw_ss (pc : Z) (rs : YP09.smem) : sstate := mkSS pc sr_atoms rs None (mkFacts [] [] []).

(* ---- the width word s7 (0x807dc .. 0x807f4), as the engine leaves it ---- *)
(* s7 = (fab <s nch) | nch | (nch - 41 <u -39): its low bit is clear exactly for Pau's legal width. *)
Definition CW_S7 : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLT (SOff 49 0) (SOff 48 0)) (SOff 48 0))
    (SAlu ALU_SLTU (SOff 48 (-41)) (SLit (-39))).
Definition cw_s7z (n f : Z) : Z :=
  zcanon (zalu_raw 63 64 ALU_OR
    (zcanon (zalu_raw 63 64 ALU_OR (zcanon (zalu_raw 63 64 ALU_SLT (zcanon (f + 0)) (zcanon (n + 0)))) (zcanon (n + 0))))
    (zcanon (zalu_raw 63 64 ALU_SLTU (zcanon (n + -41)) (zcanon (-39))))).

Lemma cw_U_s7 : forall E n f, ew E 48 = w64 n -> ew E 49 = w64 f -> 0 <= n < 2 ^ 64 -> 0 <= f < 2 ^ 64 ->
  U E CW_S7 = cw_s7z n f.
Proof.
  intros E n f H48 H49 Hn Hf. unfold CW_S7, cw_s7z.
  rewrite !U_SAlu, !U_SOff, !U_SLit, H48, H49. unfold w64. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma cw_s7_ok : forall n f, 0 <= n < 256 -> 1 <= f <= 40 ->
  Z.land (cw_s7z n f) 1 = Z.b2z (negb (LLVMFuzzerTestOneInput_case1.c1_okb n f)).
Proof.
  intros n f Hn Hf.
  assert (H : forallb (fun n => forallb (fun f => Z.land (cw_s7z n f) 1 =?
                  Z.b2z (negb (LLVMFuzzerTestOneInput_case1.c1_okb n f)))
                (map Z.of_nat (seq 1 40))) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (In_n : In n (map Z.of_nat (seq 0 256))).
  { replace n with (Z.of_nat (Z.to_nat n)) by lia. apply in_map. apply in_seq. lia. }
  specialize (H n In_n). rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  replace f with (Z.of_nat (Z.to_nat f)) by lia. apply in_map. apply in_seq. lia.
Qed.

(* bnez a0 at 0x807fc, a0 = s7 & 1. *)
Lemma cw_br1 : forall E n f, ew E 48 = w64 n -> ew E 49 = w64 f -> 0 <= n < 256 -> 1 <= f <= 40 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND CW_S7 (SLit 1))) (sv_denot E (SLit 0)) =
  negb (LLVMFuzzerTestOneInput_case1.c1_okb n f).
Proof.
  intros E n f H48 H49 Hn Hf.
  rewrite branch_ne_U, U_and_lit by lia. rewrite (cw_U_s7 E n f H48 H49) by lia.
  rewrite cw_s7_ok by lia. rewrite U_lit by lia.
  destruct (LLVMFuzzerTestOneInput_case1.c1_okb n f); reflexivity.
Qed.

Lemma cw_s7_low : forall n f, 0 <= n < 256 -> 1 <= f <= 40 ->
  (Z.land (cw_s7z n f) 1 = 0 <-> reac_boxreg_add_c.add_width_ok n f).
Proof.
  intros n f Hn Hf. rewrite cw_s7_ok by lia. rewrite <- LLVMFuzzerTestOneInput_case1.c1_okb_spec.
  destruct (LLVMFuzzerTestOneInput_case1.c1_okb n f); cbn; split; intros H; first [reflexivity | discriminate | lia].
Qed.

Lemma cw_s7_range : forall E, 0 <= U E CW_S7 < 2 ^ 64.
Proof. intros E. pose proof (U_range E CW_S7) as H. unfold M64 in H. exact H. Qed.


(* ---- the count s8 of the inlined lowest_free loop (0x80968 .. 0x80980), as the engine leaves it ---- *)
(* d = fab - nch; s8 = addiw ((-(0 <s d)) & d, 1) = max (d, 0) + 1. *)
Definition CW_D : sv := SAlu ALU_ADD (SMd M_MUL (SOff 48 0) (SLit (-1))) (SOff 49 0).
Definition CW_S8 : sv :=
  SAluw ALU_ADD (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) CW_D)) CW_D) (SLit 1).
Definition cw_dz (n f : Z) : Z :=
  zcanon (zalu_raw 63 64 ALU_ADD (zcanon (zmd_raw 64 M_MUL (zcanon (n + 0)) (zcanon (-1)))) (zcanon (f + 0))).
Definition cw_s8z (n f : Z) : Z :=
  bv_wrap 64 (bv_swrap 32 (zalu_raw 31 32 ALU_ADD
    (zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_SUB (zcanon 0)
       (zcanon (zalu_raw 63 64 ALU_SLT (zcanon 0) (cw_dz n f))))) (cw_dz n f)) mod 2 ^ 32)
    (zcanon 1 mod 2 ^ 32))).

Lemma cw_U_s8 : forall E n f, ew E 48 = w64 n -> ew E 49 = w64 f -> 0 <= n < 2 ^ 64 -> 0 <= f < 2 ^ 64 ->
  U E CW_S8 = cw_s8z n f.
Proof.
  intros E n f H48 H49 Hn Hf. unfold CW_S8, cw_s8z, cw_dz, CW_D.
  rewrite U_of_S, S_SAluw, !U_SAlu, !U_SMd, !U_SOff, !U_SLit, H48, H49. unfold w64.
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma cw_s8_val : forall n f, 2 <= n <= 40 -> n <= f <= 40 -> cw_s8z n f = f - n + 1.
Proof.
  intros n f Hn Hf.
  assert (H : forallb (fun n => forallb (fun f => (f <? n) || (cw_s8z n f =? f - n + 1))
                (map Z.of_nat (seq 0 41))) (map Z.of_nat (seq 0 41)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (In_n : In n (map Z.of_nat (seq 0 41))).
  { replace n with (Z.of_nat (Z.to_nat n)) by lia. apply in_map. apply in_seq. lia. }
  specialize (H n In_n). rewrite forallb_forall in H.
  assert (In_f : In f (map Z.of_nat (seq 0 41))).
  { replace f with (Z.of_nat (Z.to_nat f)) by lia. apply in_map. apply in_seq. lia. }
  specialize (H f In_f). apply orb_true_iff in H as [H | H]; [apply Z.ltb_lt in H; lia | apply Z.eqb_eq; exact H].
Qed.

Lemma cw_denot_s8 : forall E n f, ew E 48 = w64 n -> ew E 49 = w64 f -> 2 <= n <= 40 -> n <= f <= 40 ->
  sv_denot E CW_S8 = w64 (f - n + 1).
Proof.
  intros E n f H48 H49 Hn Hf. rewrite denot_lit_U, (cw_U_s8 E n f H48 H49) by lia. rewrite cw_s8_val by lia.
  reflexivity.
Qed.

(* ---- the branches, decided on the words their operands denote ---- *)
Lemma cw_m1 : Z_to_bv 64 18446744073709551615 = w64 (-1).
Proof. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma cw_denot_lit : forall E z, sv_denot E (SLit z) = w64 z.
Proof. intros E z. reflexivity. Qed.

Lemma cw_br_lt : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof. intros E a b x y Ha Hb Hx Hy. cbn [branch_taken]. rewrite Ha, Hb. apply Boxreg.lts_lit; lia. Qed.

Lemma cw_br_ge : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof. intros E a b x y Ha Hb Hx Hy. cbn [branch_taken]. rewrite Ha, Hb. f_equal. apply Boxreg.lts_lit; lia. Qed.

Lemma cw_br_eq : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (x =? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite branch_eq_U. unfold U. rewrite Ha, Hb. unfold w64.
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma cw_br_ne : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (x =? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite branch_ne_U. unfold U. rewrite Ha, Hb. unfold w64.
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* ---- the tactics of the walk ---- *)
(* A register of a symbolic state as the term the state holds (no normalization). *)
Ltac cw_rawreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* After a run over read-only regions: the memory is the one before. *)
Ltac cw_ro HM :=
  lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
    pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* A register goal of a landing, from the register's value prreg gave and the seat's facts (ER: the seat's
   atoms 0 .. 31 are the cut's registers). *)
Ltac cw_reg_close ER :=
  first
  [ match goal with Q : getr (ms_regs ?m) ?n = ew ?E ?a |- getr (ms_regs ?m) ?n = _ =>
      rewrite Q; first [ rewrite (ER a n eq_refl); assumption | assumption ] end
  | match goal with Q : getr (ms_regs ?m) ?n = _ |- getr (ms_regs ?m) ?n = _ =>
      rewrite Q; first [exact cw_m1 | reflexivity | assumption] end ].


(* ---- the lf loop's seat: the slot lf (sp1 + 0x20, written by the hit) and the slot nch (sp1 + 0x50) ---- *)
Definition CW_LSL20 : list (Z * sv) := [(0x20, SLit (2 ^ 64 - 1))].
Definition CW_R20 : YP09.region := YP09.mkRegion (Some 9%nat) 0x20 0x28 0x20 0x28 (lx_slot_chunks CW_LSL20).
Definition CW_LSL50 : list (Z * sv) := [(0x50, SOff 48 0)].
Definition CW_R50 : YP09.region := YP09.mkRegion (Some 9%nat) 0x50 0x58 0 0 (lx_slot_chunks CW_LSL50).
(* sp = s1 = sp1 is above the shadow span, which sh_static_ok needs of a write window's base atom. *)
Definition CW_SPF : facts := mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 5)] [] [].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

(* A seat over the registers as atoms and a few regions of the phase's choice. *)
Lemma cw_seat : forall cx fp (W3 : world SEGS) (ms3 : machine_state) pc ex rs,
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  YP09.regions_wf rs = true ->
  Forall (YP09.region_ok SEGS (lx_env cx fp (ms_regs ms3) ex) (mrestrict (w_H W3) (ms_mem ms3))) rs ->
  YP09.pairwise_disjoint (lx_env cx fp (ms_regs ms3) ex) rs ->
  st_ok_pi SEGS VAL (lx_env cx fp (ms_regs ms3) ex) (cw_ss pc rs) (restrict (w_H W3) ms3).
Proof.
  intros cx fp W3 ms3 pc ex rs Hpc Hresv Hpend Hrom Hfregs Hfcsr Hwf Hok Hd.
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W3) (ms_mem ms3))
                     (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
      in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
    subst. reflexivity. }
  rewrite Hms. unfold cw_ss.
  apply pa_entry_st_ok_full; [apply lx_regs_ok_atoms | exact Hwf | exact Hok | exact Hd |].
  split; [exact I | split; exact I].
Qed.

(* ---- the memory the cuts speak about, and what keeps it ---- *)
(* Every byte a cut of the case reads stays, except the slot lf (sp1 + 0x20), which the lf loop's hit writes. *)
Definition cw_kept (cx : lxcx) (fp : Z) (W3 : world SEGS) (r : Z) (m m' : word -> option byte) : Prop :=
  forall a, (lsp1 cx <= a < 2 ^ 64 /\ ~ (lsp1 cx + 0x20 <= a < lsp1 cx + 0x28)) \/
    lc_p cx <= a < lc_p cx + lc_n cx \/ lF cx fp <= a < lF cx fp + 512 \/
    lSH cx fp <= a < lSH cx fp + 64 \/ r <= a < r + 288 ->
    aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma cw_kept_refl : forall cx fp W3 r m, cw_kept cx fp W3 r m m.
Proof. intros cx fp W3 r m a _. reflexivity. Qed.

Lemma cw_rdword_keep : forall (rd rd' : reader) a v,
  (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk H. rewrite (rdword_ext rd rd' a Hk). exact H. Qed.

Section k.
Variables (cx : lxcx) (fp : Z) (W3 : world SEGS) (r : Z) (ms ms' : machine_state).
Hypothesis K : cw_kept cx fp W3 r (ms_mem ms) (ms_mem ms').
Hypothesis Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47.

Lemma cw_slot_keep : forall off v, 0 <= off -> off + 8 <= 0x98 -> (off + 8 <= 0x20 \/ 0x28 <= off) ->
  lslot cx W3 ms off v -> lslot cx W3 ms' off v.
Proof.
  intros off v H0 H1 H2 Hv. unfold lslot, lview in *. eapply (cw_rdword_keep _ _ _ v); [|exact Hv].
  intros j Hj. apply K. left. split; lia.
Qed.

Lemma cw_saved_keep : lsaved cx W3 ms -> lsaved cx W3 ms'.
Proof.
  intros (Hra & Hsj). unfold lsaved, lview in *. split.
  - eapply (cw_rdword_keep _ _ _ _); [|exact Hra]. intros j Hj. apply K. left. split; lia.
  - intros j Hj. eapply (cw_rdword_keep _ _ _ _); [|exact (Hsj j Hj)]. intros q Hq. apply K. left. split; lia.
Qed.

Lemma cw_shadow_keep : lshadow cx fp W3 ms LSH_iter -> lshadow cx fp W3 ms' LSH_iter.
Proof.
  intros Hs j Hj. unfold lview in *. rewrite K; [exact (Hs j Hj)|].
  assert (Hl : length LSH_iter = 52%nat) by reflexivity. rewrite Hl in Hj.
  right; right; right; left. lia.
Qed.

Lemma cw_flag_keep :
  rdword (lview W3 ms) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) ->
  rdword (lview W3 ms') (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp).
Proof.
  intros Hv. assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity). rewrite Hfb in *.
  unfold lview in *. eapply (cw_rdword_keep _ _ _ _); [|exact Hv]. intros j Hj. apply K. right; right; left. lia.
Qed.

Lemma cw_input_keep :
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)) ->
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)).
Proof.
  intros Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
  intros k Hkk. assert (k = 0)%nat by lia. subst k.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite length_map in Hj.
  rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') (lc_p cx + Z.of_nat j)).
  - exact Hv0.
  - apply K. right; left. unfold lc_n. lia.
Qed.

Lemma cw_reg_keep : forall bs, lreg W3 ms r bs -> lreg W3 ms' r bs.
Proof.
  intros bs Hr q Hq. unfold lreg, lview in *. rewrite K; [exact (Hr q Hq)|].
  right; right; right; right. unfold LX_REG in Hq. lia.
Qed.

Lemma cw_prev_keep : forall bs, lprev cx fp W3 ms bs -> lprev cx fp W3 ms' bs.
Proof.
  intros bs Hp q Hq. unfold lprev, lview in *. rewrite K; [exact (Hp q Hq)|].
  right; right; left. unfold LX_REG in Hq. lia.
Qed.

Lemma cw_mac_keep : forall M, c1_mac cx fp W3 ms M -> c1_mac cx fp W3 ms' M.
Proof.
  intros M (HL & Hm). split; [exact HL|]. intros j Hj. unfold lview in *. rewrite K; [exact (Hm j Hj)|].
  right; right; left. lia.
Qed.

Lemma cw_cur_keep : forall q, lcur cx W3 ms q -> lcur cx W3 ms' q.
Proof.
  intros q (Hq & H88 & H90). split; [exact Hq|].
  split; [apply (cw_slot_keep 0x88); [lia | lia | lia | exact H88]|].
  apply (cw_slot_keep 0x90); [lia | lia | lia | exact H90].
Qed.

Lemma cw_loop_keep : forall fab, lslots_loop cx fp W3 ms r fab -> lslots_loop cx fp W3 ms' r fab.
Proof.
  intros fab (S08 & S28 & S30 & S38 & S40 & S68 & S70 & S78).
  split; [apply (cw_slot_keep 0x08); [lia | lia | lia | exact S08]|].
  split; [apply (cw_slot_keep 0x28); [lia | lia | lia | exact S28]|].
  split; [apply (cw_slot_keep 0x30); [lia | lia | lia | exact S30]|].
  split; [apply (cw_slot_keep 0x38); [lia | lia | lia | exact S38]|].
  split; [apply (cw_slot_keep 0x40); [lia | lia | lia | exact S40]|].
  split; [apply (cw_slot_keep 0x68); [lia | lia | lia | exact S68]|].
  split; [apply (cw_slot_keep 0x70); [lia | lia | lia | exact S70]|].
  apply (cw_slot_keep 0x78); [lia | lia | lia | exact S78].
Qed.

End k.


Definition cw_ssF (pc : Z) (rs : YP09.smem) (G : facts) : sstate := mkSS pc sr_atoms rs None G.
Lemma cw_seatF : forall cx fp (W3 : world SEGS) (ms3 : machine_state) pc ex rs G,
  ms_pc_val ms3 = w64 (BASE + pc) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  YP09.regions_wf rs = true ->
  Forall (YP09.region_ok SEGS (lx_env cx fp (ms_regs ms3) ex) (mrestrict (w_H W3) (ms_mem ms3))) rs ->
  YP09.pairwise_disjoint (lx_env cx fp (ms_regs ms3) ex) rs ->
  facts_ok (lx_env cx fp (ms_regs ms3) ex) G ->
  st_ok_pi SEGS VAL (lx_env cx fp (ms_regs ms3) ex) (cw_ssF pc rs G) (restrict (w_H W3) ms3).
Proof.
  intros cx fp W3 ms3 pc ex rs G Hpc Hresv Hpend Hrom Hfregs Hfcsr Hwf Hok Hd HG.
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W3) (ms_mem ms3))
                     (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
      in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
    subst. reflexivity. }
  rewrite Hms. unfold cw_ssF.
  apply pa_entry_st_ok_full; [apply lx_regs_ok_atoms | exact Hwf | exact Hok | exact Hd | exact HG].
Qed.

Definition cw_geo (cx : lxcx) (fp r : Z) : Prop :=
  0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47 /\
  4096 <= lF cx fp /\ lF cx fp + 512 <= lsp1 cx /\
  0 <= lSH cx fp /\ lSH cx fp + 64 <= lsp1 cx /\
  4096 <= r /\ r + 288 <= lsp1 cx /\
  (lc_n cx = 0 \/ (0 <= lc_p cx /\ lc_p cx + lc_n cx <= lsp1 cx)).

Lemma cw_kept_trans : forall cx fp W3 r m1 m2 m3,
  cw_kept cx fp W3 r m1 m2 -> cw_kept cx fp W3 r m2 m3 -> cw_kept cx fp W3 r m1 m3.
Proof. intros cx fp W3 r m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma cw_kept_frame : forall cx fp W3 r E rs m m', cw_geo cx fp r ->
  frame_of E rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> YP09.base_val E b + wlo <= a < YP09.base_val E b + whi ->
     lsp1 cx + 0x20 <= a < lsp1 cx + 0x28) ->
  cw_kept cx fp W3 r m m'.
Proof.
  intros cx fp W3 r E rs m m' (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) HF Hw a Ha.
  apply (kept_of_frame E rs (w_H W3) m m' (fun a => lsp1 cx + 0x20 <= a < lsp1 cx + 0x28) HF Hw a).
  - destruct Ha as [[H1 _] | [H | [H | [H | H]]]]; [lia | | lia | lia | lia].
    destruct G8 as [G8 | G8]; [unfold lc_n in *; lia | lia].
  - destruct Ha as [[_ H1] | [H | [H | [H | H]]]]; [exact H1 | | lia | lia | lia].
    destruct G8 as [G8 | G8]; [unfold lc_n in *; lia | lia].
Qed.

Lemma cw_kept_lx : forall cx fp W3 r m m', lx_keep cx fp W3 [(r, LX_REG)] m m' -> cw_kept cx fp W3 r m m'.
Proof.
  intros cx fp W3 r m m' Hk a Ha. apply Hk. unfold lx_keep_at.
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (Hfb8 : fs_frame_bytes LX_CID / 8 = 64) by (vm_compute; reflexivity).
  rewrite Hfb8, Hfb.
  destruct Ha as [[H1 _] | [H | [H | [H | H]]]]; [left; exact H1 | right; left; exact H | right; right; left; exact H
    | right; right; right; left; exact H | right; right; right; right].
  apply Exists_cons_hd. cbn [fst snd]. unfold LX_REG. lia.
Qed.


Lemma cw_mod8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
  intros a Ha. apply Z.mod_divide in Ha; [|lia]. destruct Ha as [x ->]. apply Z.mod_divide; [lia|]. exists (2 * x). lia.
Qed.
Lemma cw_achain_ly : forall ly ly' rd sp v ch, ly_top ly' = ly_top ly -> achain ly rd sp v ch -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch Ht H. unfold achain in *. rewrite Ht. exact H. Qed.
Lemma cw_layout_top : forall n ly ly', layout_le n ly ly' -> ly_top ly' = ly_top ly.
Proof. intros n ly ly' Hle. pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & Htop & _). exact Htop. Qed.

Lemma cw_denot_a0 : forall E k (regs2 : bvmap 5 word),
  sv_denot (havoc E k (map (getr regs2) CLOB)) (SOff (k + 4) 0) = getr regs2 10.
Proof.
  intros E k regs2. cbn [sv_denot]. unfold havoc. cbn [ew].
  replace (k + 4 <? k)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (k + 4 - k)%nat with 4%nat by lia.
  cbn [map CLOB nth]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma cw_addw : forall E a c x y, sv_denot E a = w64 x -> sv_denot E c = w64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 31 -> sv_denot E (SAluw ALU_ADD a c) = w64 (x + y).
Proof.
  intros E a c x y Ha Hc Hx Hy Hxy. cbn [sv_denot]. rewrite Ha, Hc. unfold w64.
  rewrite (aluw_addsub_of_lit ALU_ADD _ _ (x + y) (or_introl eq_refl) (alu64_add_lit x y)).
  f_equal. unfold zalu32, zcanon, zu32, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [zalu_raw].
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
  unfold M32. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648.
  change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.
Lemma cw_atom0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v.
Proof.
  intros E n v H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv.
  rewrite Z.add_0_r. reflexivity.
Qed.

Ltac cw_kd cx fp WW rr Ex GEO UB K :=
  lazymatch goal with
  | HFx : frame_of _ _ (mrestrict _ ?m) (mrestrict _ ?m') |- _ =>
    assert (K : cw_kept cx fp WW rr m m');
    [ eapply (cw_kept_frame cx fp WW rr Ex _ _ _ GEO);
      [ exact HFx
      | let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in
        let a := fresh "a" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Hx := fresh "Hx" in
        intros bb wlo whi a Hin Hr;
        cbn [windows map CW_R20 CW_R50 YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin;
        destruct Hin as [Hx | [Hx | []]]; injection Hx as <- <- <-;
        cbn [YP09.base_val] in Hr; rewrite UB in Hr; lia ]
    | ]
  end.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma cw_geo_of : forall cx fp W3 (ms3 : machine_state) ly3 S3 md3 k r,
  lx_base B MT cx -> AR_laws SEGS B ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] -> lblk B cx ly3 S3 r -> cw_geo cx fp r.
Proof.
  intros cx fp W3 ms3 ly3 S3 md3 k r HB LAWS HJ HFR Hblk.
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & _ & HFal & HSHeq).
  pose proof asan_consts as (C1a & _).
  pose proof HJ as (HAR3 & _).
  assert (Hrin3 : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite Hblk; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin3) as (_ & Hr4096 & Hrceil & _ & _ & _).
  change (req_size LX_REG) with 288 in Hrceil.
  assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : lF cx fp / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [rewrite HSHeq; unfold SHADOW_OFF; lia|]. split; [rewrite HSHeq; unfold SHADOW_OFF; lia|].
  split; [lia|]. split; [lia|].
  destruct HB as (_ & _ & _ & Hpn & _). destruct Hpn as [[Hn0 _] | (Hn & Hin)]; [left; exact Hn0 | right].
  assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)) by (rewrite Hblk; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. lia.
Qed.

(* ---- the landings ---- *)
(* At C1_P7 (0x809a8): the cut's memory facts from the state ms of an earlier cut and the bytes kept since. *)
Lemma cw_to7 : forall POST i cx fp k acc ly3 S3 W3 (ms : machine_state) (m' : word -> option byte) md'
  (regs' : bvmap 5 word) (q : nat) r fab bs M nch nz lf want w7 pc0,
  lx_from B MT POST (C1_I7 B MT i) ->
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m' md' k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  c1_body B MT i cx fp pc0 k acc ly3 S3 W3 ms r fab bs q ->
  c1_read cx fp W3 ms M nch -> c1_nz cx W3 ms M nz ->
  cw_kept cx fp W3 r (ms_mem ms) m' ->
  rdword (aview SEGS (w_H W3) m') (lsp1 cx + 0x20) = Some (lf mod 2 ^ 64) -> -1 <= lf <= 38 ->
  LC1.c1_wantP bs M nch lf want -> -1 <= want <= 4 ->
  0 <= w7 < 2 ^ 64 -> (Z.land w7 1 = 0 <-> reac_boxreg_add_c.add_width_ok nch fab) ->
  getr regs' 2 = w64 (lsp1 cx) -> getr regs' 8 = w64 (lsp0 cx) -> getr regs' 9 = w64 (lsp1 cx) ->
  getr regs' 3 = getr (lc_regs cx) 3 -> getr regs' 4 = getr (lc_regs cx) 4 ->
  getr regs' 18 = w64 SHADOW_OFF -> getr regs' 22 = w64 (lSH cx fp) ->
  getr regs' 20 = w64 r -> getr regs' 21 = w64 (lF cx fp + 64) ->
  getr regs' 23 = w64 w7 -> getr regs' 25 = w64 want -> getr regs' 26 = w64 (Boxreg.bx_n bs) ->
  getr regs' 27 = w64 fab ->
  SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + C1_P7)) m' (seg_rom SEGS)) md') (POST cx).
Proof.
  intros POST i cx fp k acc ly3 S3 W3 ms m' md' regs' q r fab bs M nch nz lf want w7 pc0
    HN7 HB HJ HFR HMO HBODY HREAD HNZ HK S20 Hlf HWP Hwant Hw7 Hw7i
    G2 G8 G9 G3 G4 G18 G22 G20 G21 G23 G25 G26 G27.
  set (ms' := mkst regs' (Z_to_bv 64 (BASE + C1_P7)) m' (seg_rom SEGS)).
  apply (HN7 cx fp k acc ly3 S3 W3 ms' md' HB HJ HFR HMO).
  pose proof (lx_sp_facts B MT cx HB) as (_ & Hsp0lo & Hsp0hi & Hsp1 & _).
  pose proof asan_consts as (C1a & _).
  assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
  assert (K : cw_kept cx fp W3 r (ms_mem ms) (ms_mem ms')) by exact HK.
  destruct HBODY as (HBD & Hi & Hk & Hacc & HBLK & HREG & HINV & HFAB & HPREV & HCUR & HSLL & S58 & S48 & R20 & R21).
  destruct HBD as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSHD & HFLAG & HS10 & HS18 & HS80 & HINP).
  destruct HREAD as (HMAC & S50 & Hnch). destruct HNZ as (S60 & Hnz & Hnzi).
  exists q, r, fab, bs, M, nch, nz, lf, want, w7.
  split; [|split; [|split; [|split]]].
  - split; [|split; [exact Hi|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HBLK|]].
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 G22))))))|].
      split; [exact (cw_saved_keep cx fp W3 r ms ms' K Hsp HSAVED)|].
      split; [exact (cw_shadow_keep cx fp W3 r ms ms' K HSHD)|].
      split; [exact (cw_flag_keep cx fp W3 r ms ms' K HFLAG)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x10 _ ltac:(lia) ltac:(lia) ltac:(lia) HS10)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x18 _ ltac:(lia) ltac:(lia) ltac:(lia) HS18)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x80 _ ltac:(lia) ltac:(lia) ltac:(lia) HS80)|].
      exact (cw_input_keep cx fp W3 r ms ms' K HINP).
    + split; [exact (cw_reg_keep cx fp W3 r ms ms' K bs HREG)|].
      split; [exact HINV|]. split; [exact HFAB|].
      split; [exact (cw_prev_keep cx fp W3 r ms ms' K bs HPREV)|].
      split; [exact (cw_cur_keep cx fp W3 r ms ms' K Hsp q HCUR)|].
      split; [exact (cw_loop_keep cx fp W3 r ms ms' K Hsp fab HSLL)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x58 _ ltac:(lia) ltac:(lia) ltac:(lia) S58)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x48 _ ltac:(lia) ltac:(lia) ltac:(lia) S48)|].
      split; [exact G20 | exact G21].
  - split; [exact (cw_mac_keep cx fp W3 r ms ms' K M HMAC)|].
    split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x50 _ ltac:(lia) ltac:(lia) ltac:(lia) S50) | exact Hnch].
  - split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x60 _ ltac:(lia) ltac:(lia) ltac:(lia) S60)|].
    split; [exact Hnz | exact Hnzi].
  - exact S20.
  - split; [exact Hlf|]. split; [exact HWP|]. split; [exact Hwant|]. split; [exact Hw7|]. split; [exact Hw7i|].
    split; [exact G23|]. split; [exact G25|]. split; [exact G26 | exact G27].
Qed.

(* C1_I6's predicate with its witnesses as arguments. *)
Definition cw_I6b (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (q : nat) (r fab : Z) (bs M : list byte) (nch nz b w7 : Z) : Prop :=
  c1_body B MT i cx fp C1_P6 k acc ly3 S3 W3 ms3 r fab bs q /\
  c1_read cx fp W3 ms3 M nch /\ c1_nz cx W3 ms3 M nz /\
  lslot cx W3 ms3 0x20 (2 ^ 64 - 1) /\
  reac_boxreg_add_c.add_width_ok nch fab /\ M <> Boxreg.zero6 /\
  reac_boxreg_add_c.add_none_held bs M /\ reac_boxreg_add_c.add_none_unbound bs nch /\
  Boxreg.bx_n bs < 5 /\ lxc1_lfinv bs nch fab b /\ 0 <= b <= fab - nch /\
  0 <= w7 < 2 ^ 64 /\ Z.land w7 1 = 0 /\ getr (ms_regs ms3) 23 = w64 w7 /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 24 = w64 (fab - nch + 1) /\
  getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\ getr (ms_regs ms3) 27 = w64 fab.

Lemma cw_I6_of : forall i cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz b w7,
  cw_I6b i cx fp k acc ly3 S3 W3 ms3 q r fab bs M nch nz b w7 -> C1_I6 B MT i cx fp k acc ly3 S3 W3 ms3 md3.
Proof.
  intros i cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz b w7 H.
  exists q, r, fab, bs, M, nch, nz, b, w7. exact H.
Qed.

(* At C1_P6 (0x80984), as cw_to7. *)
Lemma cw_to6 : forall i cx fp k acc ly3 S3 W3 (ms : machine_state) (m' : word -> option byte)
  (regs' : bvmap 5 word) (q : nat) r fab bs M nch nz b w7 pc0,
  lx_base B MT cx ->
  c1_body B MT i cx fp pc0 k acc ly3 S3 W3 ms r fab bs q ->
  c1_read cx fp W3 ms M nch -> c1_nz cx W3 ms M nz ->
  cw_kept cx fp W3 r (ms_mem ms) m' ->
  rdword (aview SEGS (w_H W3) m') (lsp1 cx + 0x20) = Some (2 ^ 64 - 1) ->
  reac_boxreg_add_c.add_width_ok nch fab -> M <> Boxreg.zero6 ->
  reac_boxreg_add_c.add_none_held bs M -> reac_boxreg_add_c.add_none_unbound bs nch ->
  Boxreg.bx_n bs < 5 -> lxc1_lfinv bs nch fab b -> 0 <= b <= fab - nch ->
  0 <= w7 < 2 ^ 64 -> Z.land w7 1 = 0 ->
  getr regs' 2 = w64 (lsp1 cx) -> getr regs' 8 = w64 (lsp0 cx) -> getr regs' 9 = w64 (lsp1 cx) ->
  getr regs' 3 = getr (lc_regs cx) 3 -> getr regs' 4 = getr (lc_regs cx) 4 ->
  getr regs' 18 = w64 SHADOW_OFF -> getr regs' 22 = w64 (lSH cx fp) ->
  getr regs' 20 = w64 r -> getr regs' 21 = w64 (lF cx fp + 64) ->
  getr regs' 23 = w64 w7 -> getr regs' 19 = w64 b -> getr regs' 24 = w64 (fab - nch + 1) ->
  getr regs' 26 = w64 (Boxreg.bx_n bs) -> getr regs' 27 = w64 fab ->
  cw_I6b i cx fp k acc ly3 S3 W3 (mkst regs' (Z_to_bv 64 (BASE + C1_P6)) m' (seg_rom SEGS))
    q r fab bs M nch nz b w7.
Proof.
  intros i cx fp k acc ly3 S3 W3 ms m' regs' q r fab bs M nch nz b w7 pc0
    HB HBODY HREAD HNZ HK S20 Hok HM0 Hnh Hnu Hn5 Hlfi Hb Hw7 Hw70
    G2 G8 G9 G3 G4 G18 G22 G20 G21 G23 G19 G24 G26 G27.
  set (ms' := mkst regs' (Z_to_bv 64 (BASE + C1_P6)) m' (seg_rom SEGS)).
  pose proof (lx_sp_facts B MT cx HB) as (_ & Hsp0lo & Hsp0hi & Hsp1 & _).
  pose proof asan_consts as (C1a & _).
  assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
  assert (K : cw_kept cx fp W3 r (ms_mem ms) (ms_mem ms')) by exact HK.
  destruct HBODY as (HBD & Hi & Hk & Hacc & HBLK & HREG & HINV & HFAB & HPREV & HCUR & HSLL & S58 & S48 & R20 & R21).
  destruct HBD as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSHD & HFLAG & HS10 & HS18 & HS80 & HINP).
  destruct HREAD as (HMAC & S50 & Hnch). destruct HNZ as (S60 & Hnz & Hnzi).
  split; [|split; [|split; [|split]]].
  - split; [|split; [exact Hi|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HBLK|]].
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 G22))))))|].
      split; [exact (cw_saved_keep cx fp W3 r ms ms' K Hsp HSAVED)|].
      split; [exact (cw_shadow_keep cx fp W3 r ms ms' K HSHD)|].
      split; [exact (cw_flag_keep cx fp W3 r ms ms' K HFLAG)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x10 _ ltac:(lia) ltac:(lia) ltac:(lia) HS10)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x18 _ ltac:(lia) ltac:(lia) ltac:(lia) HS18)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x80 _ ltac:(lia) ltac:(lia) ltac:(lia) HS80)|].
      exact (cw_input_keep cx fp W3 r ms ms' K HINP).
    + split; [exact (cw_reg_keep cx fp W3 r ms ms' K bs HREG)|].
      split; [exact HINV|]. split; [exact HFAB|].
      split; [exact (cw_prev_keep cx fp W3 r ms ms' K bs HPREV)|].
      split; [exact (cw_cur_keep cx fp W3 r ms ms' K Hsp q HCUR)|].
      split; [exact (cw_loop_keep cx fp W3 r ms ms' K Hsp fab HSLL)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x58 _ ltac:(lia) ltac:(lia) ltac:(lia) S58)|].
      split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x48 _ ltac:(lia) ltac:(lia) ltac:(lia) S48)|].
      split; [exact G20 | exact G21].
  - split; [exact (cw_mac_keep cx fp W3 r ms ms' K M HMAC)|].
    split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x50 _ ltac:(lia) ltac:(lia) ltac:(lia) S50) | exact Hnch].
  - split; [exact (cw_slot_keep cx fp W3 r ms ms' K Hsp 0x60 _ ltac:(lia) ltac:(lia) ltac:(lia) S60)|].
    split; [exact Hnz | exact Hnzi].
  - exact S20.
  - repeat (split; [eassumption|]). exact G27.
Qed.

(* ---- c1_seg_want: 0x807dc (C1_P5) -> 0x80984 (C1_P6) or 0x809a8 (C1_P7) ----
   The seat: the registers as atoms 0 .. 31 (s3 = bind, s9 = held), and one read-only region over the spill slots
   the segment reads: fab (sp1 + 0x30), n_before (+ 0x48), nch (+ 0x50) and nonzero (+ 0x60), as atoms 48 .. 51.
   No instruction of the segment stores, checks a shadow byte or traps; every run leaves the memory as it was. The
   branches: 0x807fc bnez (s7 & 1) (the width word, cw_br1), 0x80808 beqz nonzero, 0x8080c bgez held,
   0x80810 bltz bind, 0x80964 blt 4, n_before. *)
Theorem c1_seg_want : C1_SEG_want B MT.
Proof.
intros HY POST i HN6 HN7 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
pose proof (lh_laws B MT HY) as LAWS.
destruct HGI as (q & r & fab & bs & M & nch & nz & h & u & HBODY1 & HREAD & HNZ & S20 & HSH & HSU & R19 & R25).
pose proof HBODY1 as (HBODY & Hi64 & Hk & Hacc & HBLK & HREG & HINV & HFAB & HPREV & HCUR & HSLL & S58 & S48 & R20 & R21).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSHD & HFLAG
  & HS10 & HS18 & HS80 & HINP).
pose proof HREAD as (HMAC & S50 & Hnch).
pose proof HNZ as (S60 & Hnz & Hnzi).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HINV as ((HLEN & HB1 & HB2 & HB3 & _) & _).
unfold Boxreg.boxreg_B1 in HB1. unfold Boxreg.boxreg_B2 in HB2.
set (ex := [w64 nch; w64 fab; w64 (Boxreg.bx_n bs); w64 nz]).
remember (lx_env cx fp (ms_regs ms3) ex) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply lx_env_img).
assert (E9 : ew E 9 = w64 (lsp1 cx)) by (rewrite HE, (lx_env_reg cx fp _ ex 9 (Z_to_bv 5 9)) by reflexivity; exact G9).
assert (E48 : ew E 48 = w64 nch) by (rewrite HE; exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia))).
assert (E49 : ew E 49 = w64 fab) by (rewrite HE; exact (lx_env_ex cx fp (ms_regs ms3) ex 1 ltac:(lia))).
assert (E50 : ew E 50 = w64 (Boxreg.bx_n bs)) by (rewrite HE; exact (lx_env_ex cx fp (ms_regs ms3) ex 2 ltac:(lia))).
assert (E51 : ew E 51 = w64 nz) by (rewrite HE; exact (lx_env_ex cx fp (ms_regs ms3) ex 3 ltac:(lia))).
assert (HSL : lx_slots cx W3 ms3 E CW_SLOTS).
{ unfold lx_slots, CW_SLOTS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - apply (lx_slot_atom cx W3 ms3 E 0x30 49 fab 0); [rewrite Z.add_0_r; exact L30 | exact E49 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x48 50 (Boxreg.bx_n bs) 0); [rewrite Z.add_0_r; exact S48 | exact E50 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x50 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x60 51 nz 0); [rewrite Z.add_0_r; exact S60 | exact E51 | lia | lia]. }
assert (HR : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) CW_REG).
{ unfold YP09.region_ok, CW_REG. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  exact (lx_slot_chunks_ok cx W3 ms3 E CW_SLOTS HSL). }
assert (HS : st_ok_pi SEGS VAL E (cw_ss C1_P5 [CW_REG]) (restrict (w_H W3) ms3)).
{ rewrite HE. rewrite HE in HR. apply cw_seat; try assumption.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HR | apply Forall_nil].
  - cbn. tauto. }
assert (SHOK : sh_ok SEGS CW_BX [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose (RUN := paj_run B LAWS).
paj_run_tok RUN HS HJ SHOK CW_BSPAN; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].

pose (BR := paj_branch (PI := PI)).
pose (RUNTO := paj_run_to B LAWS).
assert (ER : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr (ms_regs ms3) rr)
  by (intros n rr Hn; rewrite HE; apply lx_env_reg; exact Hn).
cw_ro HM1. clear HEI0.
psrr_branch_tok RUN BR HS SHOK CW_BSPAN.
all: fold CW_S7 in Hc; rewrite (cw_br1 E nch fab E48 E49 Hnch) in Hc by lia.

1: { paj_run_to_tok RUNTO HS HJ SHOK CW_BSPAN C1_P7; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM2. clear HEI0.

pmkst HS.
cw_rawreg HS (23%bv : bv 5) Q23. fold CW_S7 in Q23. rewrite denot_lit_U, (cw_U_s7 E nch fab E48 E49) in Q23 by lia.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
repeat match goal with HMx : ms_mem ?a = ms_mem ?b |- _ => rewrite HMx in HJ |- *; clear HMx end.

apply (cw_to7 POST i cx fp k acc ly3 S3 W3 ms3 (ms_mem ms3) _ _ q r fab bs M nch nz (-1) (-1)
  (cw_s7z nch fab) C1_P5 HN7 HB HJ HFR HMO HBODY1 HREAD HNZ (cw_kept_refl _ _ _ _ _));
[ unfold lslot, lview in S20; replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity; exact S20
| lia
| left; split; [|reflexivity]; intros (Hok & _); rewrite HFAB in Hok;
  apply LLVMFuzzerTestOneInput_case1.c1_okb_spec in Hok; rewrite Hok in Hc; discriminate
| lia
| rewrite <- (cw_U_s7 E nch fab E48 E49) by lia; apply cw_s7_range
| apply cw_s7_low; lia
| cw_reg_close ER .. ]. }

assert (Hok : reac_boxreg_add_c.add_width_ok nch fab).
{ apply LLVMFuzzerTestOneInput_case1.c1_okb_spec. destruct (LLVMFuzzerTestOneInput_case1.c1_okb nch fab); [reflexivity | discriminate]. }
clear Hc.
paj_run_tok RUN HS HJ SHOK CW_BSPAN; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM2. clear HEI0.
psrr_branch_tok RUN BR HS SHOK CW_BSPAN.
all: rewrite (cw_br_eq E (SOff 51 0) (SLit 0) nz 0) in Hc by (first [rewrite lx_sv_SOff0; exact E51 | apply cw_denot_lit | lia]).

(* nonzero = 0: the MAC is zero; 0x809a4 s9 = -1 *)
1: { apply Z.eqb_eq in Hc.
paj_run_to_tok RUNTO HS HJ SHOK CW_BSPAN C1_P7; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM3. clear HEI0.

pmkst HS.
cw_rawreg HS (23%bv : bv 5) Q23. fold CW_S7 in Q23. rewrite denot_lit_U, (cw_U_s7 E nch fab E48 E49) in Q23 by lia.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
repeat match goal with HMx : ms_mem ?a = ms_mem ?b |- _ => rewrite HMx in HJ |- *; clear HMx end.

apply (cw_to7 POST i cx fp k acc ly3 S3 W3 ms3 (ms_mem ms3) _ _ q r fab bs M nch nz (-1) (-1)
  (cw_s7z nch fab) C1_P5 HN7 HB HJ HFR HMO HBODY1 HREAD HNZ (cw_kept_refl _ _ _ _ _));
[ unfold lslot, lview in S20; replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity; exact S20
| lia
| left; split; [|reflexivity]; intros (_ & HM0); apply HM0; apply Hnzi; exact Hc
| lia
| rewrite <- (cw_U_s7 E nch fab E48 E49) by lia; apply cw_s7_range
| apply cw_s7_low; lia
| cw_reg_close ER .. ]. }

assert (Hnz0 : nz <> 0) by (intros Hz; rewrite Hz in Hc; discriminate). clear Hc.
assert (HM0 : M <> Boxreg.zero6) by (intros HMz; apply Hnz0; apply Hnzi; exact HMz).
pose proof (lxc1_sh_bound bs M nz _ h HSH) as Hhb. pose proof (lxc1_su_bound bs nch _ u HSU) as Hub.
assert (E25 : ew E 25 = w64 h) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
assert (E19 : ew E 19 = w64 u) by (rewrite (ER 19%nat 19%bv eq_refl); exact R19).
paj_run_tok RUN HS HJ SHOK CW_BSPAN; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM3. clear HEI0.
psrr_branch_tok RUN BR HS SHOK CW_BSPAN.
all: rewrite (cw_br_ge E (SOff 25 0) (SLit 0) h 0) in Hc by (first [rewrite lx_sv_SOff0; exact E25 | apply cw_denot_lit | lia]).

(* held >= 0: want = held *)
1: { assert (Hh0 : 0 <= h) by (destruct (Z.ltb_spec h 0); [discriminate | lia]). clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK CW_BSPAN C1_P7; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM4. clear HEI0.

pmkst HS.
cw_rawreg HS (23%bv : bv 5) Q23. fold CW_S7 in Q23. rewrite denot_lit_U, (cw_U_s7 E nch fab E48 E49) in Q23 by lia.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
repeat match goal with HMx : ms_mem ?a = ms_mem ?b |- _ => rewrite HMx in HJ |- *; clear HMx end.

apply (cw_to7 POST i cx fp k acc ly3 S3 W3 ms3 (ms_mem ms3) _ _ q r fab bs M nch nz (-1) h
  (cw_s7z nch fab) C1_P5 HN7 HB HJ HFR HMO HBODY1 HREAD HNZ (cw_kept_refl _ _ _ _ _));
[ unfold lslot, lview in S20; replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity; exact S20
| lia
| right; left; rewrite HFAB; split; [exact Hok|]; split; [exact HM0 | exact (lxc1_held_pos bs M nz h HSH Hh0)]
| lia
| rewrite <- (cw_U_s7 E nch fab E48 E49) by lia; apply cw_s7_range
| apply cw_s7_low; lia
| cw_reg_close ER .. ]. }

assert (Hh0 : h < 0) by (destruct (Z.ltb_spec h 0); [lia | discriminate]). clear Hc.
pose proof (lxc1_held_neg bs M nz h HSH Hh0 Hnz0) as Hnh.
paj_run_tok RUN HS HJ SHOK CW_BSPAN; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM4. clear HEI0.
psrr_branch_tok RUN BR HS SHOK CW_BSPAN.
all: rewrite (cw_br_lt E (SOff 19 0) (SLit 0) u 0) in Hc by (first [rewrite lx_sv_SOff0; exact E19 | apply cw_denot_lit | lia]).

(* bind >= 0: want = bind (0x80814 mv s9, s3) *)
2: { assert (Hu0 : 0 <= u) by (destruct (Z.ltb_spec u 0); [discriminate | lia]). clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK CW_BSPAN C1_P7; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM5. clear HEI0.

pmkst HS.
cw_rawreg HS (23%bv : bv 5) Q23. fold CW_S7 in Q23. rewrite denot_lit_U, (cw_U_s7 E nch fab E48 E49) in Q23 by lia.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
repeat match goal with HMx : ms_mem ?a = ms_mem ?b |- _ => rewrite HMx in HJ |- *; clear HMx end.

apply (cw_to7 POST i cx fp k acc ly3 S3 W3 ms3 (ms_mem ms3) _ _ q r fab bs M nch nz (-1) u
  (cw_s7z nch fab) C1_P5 HN7 HB HJ HFR HMO HBODY1 HREAD HNZ (cw_kept_refl _ _ _ _ _));
[ unfold lslot, lview in S20; replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity; exact S20
| lia
| right; right; left; rewrite HFAB; split; [exact Hok|]; split; [exact HM0|]; split; [exact Hnh | exact (lxc1_unb_pos bs nch u HSU Hu0)]
| lia
| rewrite <- (cw_U_s7 E nch fab E48 E49) by lia; apply cw_s7_range
| apply cw_s7_low; lia
| cw_reg_close ER .. ]. }

assert (Hu0 : u < 0) by (destruct (Z.ltb_spec u 0); [lia | discriminate]). clear Hc.
pose proof (lxc1_unb_neg bs nch u HSU Hu0) as Hnu.
paj_run_tok RUN HS HJ SHOK CW_BSPAN; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM5. clear HEI0.
psrr_branch_tok RUN BR HS SHOK CW_BSPAN.
all: rewrite (cw_br_lt E (SLit 4) (SOff 50 0) 4 (Boxreg.bx_n bs)) in Hc by (first [rewrite lx_sv_SOff0; exact E50 | apply cw_denot_lit | lia]).

(* n_before > 4: no room; 0x809a4 s9 = -1 *)
1: { assert (Hn5 : 5 <= Boxreg.bx_n bs) by (destruct (Z.ltb_spec 4 (Boxreg.bx_n bs)); [lia | discriminate]). clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK CW_BSPAN C1_P7; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM6. clear HEI0.

pmkst HS.
cw_rawreg HS (23%bv : bv 5) Q23. fold CW_S7 in Q23. rewrite denot_lit_U, (cw_U_s7 E nch fab E48 E49) in Q23 by lia.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
repeat match goal with HMx : ms_mem ?a = ms_mem ?b |- _ => rewrite HMx in HJ |- *; clear HMx end.

apply (cw_to7 POST i cx fp k acc ly3 S3 W3 ms3 (ms_mem ms3) _ _ q r fab bs M nch nz (-1) (-1)
  (cw_s7z nch fab) C1_P5 HN7 HB HJ HFR HMO HBODY1 HREAD HNZ (cw_kept_refl _ _ _ _ _));
[ unfold lslot, lview in S20; replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity; exact S20
| lia
| right; right; right; left; rewrite HFAB; split; [exact Hok|]; split; [exact HM0|]; split; [exact Hnh|];
  split; [exact Hnu|]; split; [left; exact Hn5 | reflexivity]
| lia
| rewrite <- (cw_U_s7 E nch fab E48 E49) by lia; apply cw_s7_range
| apply cw_s7_low; lia
| cw_reg_close ER .. ]. }

(* room for a row: 0x80968 .. 0x80980, b = 0, s8 = max (fab - nch, 0) + 1, the loop head *)
assert (Hn4 : Boxreg.bx_n bs < 5) by (destruct (Z.ltb_spec 4 (Boxreg.bx_n bs)); [discriminate | lia]). clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK CW_BSPAN C1_P6; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
cw_ro HM6. clear HEI0.
pmkst HS.
cw_rawreg HS (23%bv : bv 5) Q23. fold CW_S7 in Q23. rewrite denot_lit_U, (cw_U_s7 E nch fab E48 E49) in Q23 by lia.
cw_rawreg HS (24%bv : bv 5) Q24. fold CW_D in Q24. fold CW_S8 in Q24.
pose proof Hok as (_ & Hk40 & Hkf).
rewrite (cw_denot_s8 E nch fab E48 E49) in Q24 by lia.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (19%bv : bv 5) Q19. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
repeat match goal with HMx : ms_mem ?a = ms_mem ?b |- _ => rewrite HMx in HJ |- *; clear HMx end.
lazymatch goal with |- SRr _ _ (mkCfg ?m ?d) _ => apply (HN6 cx fp k acc ly3 S3 W3 m d HB HJ HFR HMO) end.
apply (cw_I6_of i cx fp k acc ly3 S3 W3 _ _ q r fab bs M nch nz 0 (cw_s7z nch fab)).
apply (cw_to6 i cx fp k acc ly3 S3 W3 ms3 (ms_mem ms3) _ q r fab bs M nch nz 0 (cw_s7z nch fab) C1_P5
  HB HBODY1 HREAD HNZ (cw_kept_refl _ _ _ _ _));
[ unfold lslot, lview in S20; exact S20
| exact Hok | exact HM0 | exact Hnh | exact Hnu | exact Hn4 | apply lxc1_lf0 | lia
| rewrite <- (cw_U_s7 E nch fab E48 E49) by lia; apply cw_s7_range
| apply (proj2 (cw_s7_low nch fab ltac:(lia) ltac:(lia))); exact Hok
| cw_reg_close ER .. ].
Qed.


(* ---- c1_seg_lf: the inlined lowest_free loop, 0x80984 (C1_P6) -> 0x80984 or 0x809a8 (C1_P7) ----
   The seat: the registers as atoms 0 .. 31 (s3 = b, s8 = fab - nch + 1, s10 = n_before, s11 = fab), the slot nch
   (sp1 + 0x50) as atom 48, a writable region over the slot lf (sp1 + 0x20, which the hit writes) and a read-only
   one over nch; the fact that sp = s1 is above the shadow span (CW_SPF), which sh_static_ok asks of a write
   window's base atom. The round: 0x80984 .. 0x80990 the four arguments (prev, b, nch, fab), 0x80994 the call of
   range_free (lh_range_free through YC85.v cl_callS; prev is an object of the side-stack frame, lx_shent_frame),
   0x80998 `bnez a0` (range_free's own result, no guard of this walk), and either 0x80d60 (the hit: `sd s3,0x20(s1)`
   and `mv s9,s10`, then 0x809a8) or 0x8099c `addiw s3,s3,1` and 0x809a0 `bne s8,s3` (the loop, or 0x809a4 with
   s9 = -1). The recursion is on Z.to_nat (fab - nch + 1 - b). *)

Lemma cw_lf_n : forall POST i, lx_hyps B MT -> lx_from B MT POST (C1_I7 B MT i) ->
  forall (n : nat) cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz b w7,
  (Z.to_nat (fab - nch + 1 - b) <= n)%nat ->
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  cw_I6b i cx fp k acc ly3 S3 W3 ms3 q r fab bs M nch nz b w7 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros POST i HY HN7 n. induction n as [|n IHn];
  intros cx fp k acc ly3 S3 W3 ms3 md3 q r fab bs M nch nz b w7 Hn HB HJ HFR HMO HGI.
{ exfalso. pose proof HGI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbb & _). lia. }
pose proof (lh_laws B MT HY) as LAWS.
pose proof HGI as (HBODY1 & HREAD & HNZ & S20 & Hok & HM0 & Hnh & Hnu & Hn5 & Hlfi & Hb & Hw7 & Hw70
  & R23 & R19 & R24 & R26 & R27).
pose proof HBODY1 as (HBODY & Hi64 & Hk & Hacc & HBLK & HREG & HINV & HFAB & HPREV & HCUR & HSLL & S58 & S48 & R20 & R21).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSHD & HFLAG
  & HS10 & HS18 & HS80 & HINP).
pose proof HREAD as (HMAC & S50 & Hnch).
pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
pose proof HINV as ((HLEN & HB1 & HB2 & HB3 & _) & _).
unfold Boxreg.boxreg_B1 in HB1. unfold Boxreg.boxreg_B2 in HB2.
pose proof Hok as (Hev & Hk40 & Hkf).
set (ex := [w64 nch]).
remember (lx_env cx fp (ms_regs ms3) ex) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply lx_env_img).
assert (ER : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr (ms_regs ms3) rr)
  by (intros nn rr Hnn; rewrite HE; apply lx_env_reg; exact Hnn).
assert (E9 : ew E 9 = w64 (lsp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
assert (E48 : ew E 48 = w64 nch) by (rewrite HE; exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia))).
assert (UB9 : bv_unsigned (ew E 9) = lsp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (HR20 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) CW_R20).
{ unfold YP09.region_ok, CW_R20. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB9. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK. lia.
  - apply (lx_slot_chunks_ok cx W3 ms3 E CW_LSL20). unfold lx_slots, CW_LSL20. apply Forall_cons; [|apply Forall_nil].
    cbn [fst snd]. apply (lx_slot_lit cx W3 ms3 E 0x20 (2 ^ 64 - 1) S20). lia. }
assert (HR50 : YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) CW_R50).
{ unfold YP09.region_ok, CW_R50. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite UB9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply (lx_slot_chunks_ok cx W3 ms3 E CW_LSL50). unfold lx_slots, CW_LSL50. apply Forall_cons; [|apply Forall_nil].
  cbn [fst snd]. apply (lx_slot_atom cx W3 ms3 E 0x50 48 nch 0); [rewrite Z.add_0_r; exact S50 | exact E48 | lia | lia]. }
assert (HS : st_ok_pi SEGS VAL E (cw_ssF C1_P6 [CW_R20; CW_R50] CW_SPF) (restrict (w_H W3) ms3)).
{ rewrite HE. rewrite HE in HR20, HR50, UB9. apply cw_seatF; try assumption.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact HR20 | apply Forall_cons; [exact HR50 | apply Forall_nil]].
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint, CW_R20, CW_R50.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite UB9. lia.
  - split; [|split; exact I]. cbn [CW_SPF f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UB9. change (2 ^ 5) with 32. lia. }
assert (SHOK : sh_ok SEGS CW_BX [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose (RUN := paj_run B LAWS).
pose (BR := paj_branch (PI := PI)).
pose (RUNTO := paj_run_to B LAWS).

pose proof (cw_geo_of cx fp W3 ms3 ly3 S3 md3 k r HB LAWS HJ HFR HBLK) as GEO.
pose proof GEO as (Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EFA.
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & _ & HFal & HSHeq).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (rewrite HE; exact (lx_env_x cx fp (ms_regs ms3) ex 0 ltac:(lia))).
assert (E46 : ew E 46 = w64 (lF cx fp)) by (rewrite HE; exact (lx_env_x cx fp (ms_regs ms3) ex 14 ltac:(lia))).
assert (U32 : U E (SOff LA_SB 0) = SHADOW_OFF) by (apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
assert (U46 : U E (SOff LA_F 0) = lF cx fp) by (apply (U_atom E 46 (lF cx fp) E46); lia).
paj_run_tok RUN HS HJ SHOK CW_BSPAN.

1: { change (ss_mem (cw_ssF C1_P6 [CW_R20; CW_R50] CW_SPF)) with [CW_R20; CW_R50].
  eapply (awr_ok_cons_stack_off _ CW_R20 _ _ _ _ _ _ _ _ 9%nat (lsp1 cx - lsp0 cx));
    [reflexivity | rewrite UB9; lia | unfold CW_R20, LX_STK; cbn; lia | unfold CW_R20; cbn; lia |].
  apply awr_ok_cons_ro; [unfold CW_R50; cbn; lia | apply awr_ok_nil]. }
pmkst HS. rewrite pa_sigma_range_free.
prreg HS (1%bv : bv 5) CR1. prreg HS (2%bv : bv 5) CR2. prreg HS (3%bv : bv 5) CR3. prreg HS (4%bv : bv 5) CR4.
prreg HS (8%bv : bv 5) CR8. prreg HS (10%bv : bv 5) CR10. prreg HS (11%bv : bv 5) CR11. prreg HS (12%bv : bv 5) CR12.
prreg HS (13%bv : bv 5) CR13.
(* the run before the call kept every byte the cuts speak about *)
cw_kd cx fp W3 r E GEO UB9 KA.
clear HF HFr HG HEI0.
(* prev (F + 64, 288 bytes) is an object of the frame *)
assert (HOBJ : afobj SEGS B ly3 S3 W3 (ms_mem ms) (lF cx fp + 64) 288).
{ split; [|split].
  - exists LX_CID, fp. split; [rewrite HFR; left; reflexivity|]. split; [unfold LX_CID; lia|].
    rewrite EFA. split; [apply Z.mod_divide in HFal; [|lia]; destruct HFal as [z ->]; apply Z.mod_divide; [lia|]; exists (8 * z); lia|].
    split; [lia|]. change (fs_frame_bytes LX_CID) with 512. lia.
  - apply Z.mod_divide in HFal; [|lia]. destruct HFal as [z ->]. apply Z.mod_divide; [lia|]. exists (8 * z + 8). lia.
  - pose proof (lx_shent_frame B MT LAWS cx fp W3 ms ly3 S3 _ _ HB HJ HFR E 64 352 U32 U46
      (cw_shadow_keep cx fp W3 r ms3 ms KA HSHD) ltac:(right; lia)) as (HRA & _).
    cbn [she_m she_lo she_hi] in HRA. rewrite U32, U46 in HRA.
    rewrite (aview_rd_of SEGS). replace 288 with (352 - 64) by lia. exact HRA. }

pose proof (lh_range_free B MT HY) as RF.
assert (HB1' : Boxreg.boxreg_B1 bs) by exact HB1.
assert (HB2' : Boxreg.boxreg_B2 bs) by exact HB2.
assert (E2a : ew E 2 = w64 (lsp1 cx)) by (rewrite (ER 2%nat 2%bv eq_refl); exact G2).
assert (E8a : ew E 8 = w64 (lsp0 cx)) by (rewrite (ER 8%nat 8%bv eq_refl); exact G8).
assert (E21 : ew E 21 = w64 (lF cx fp + 64)) by (rewrite (ER 21%nat 21%bv eq_refl); exact R21).
assert (E19 : ew E 19 = w64 b) by (rewrite (ER 19%nat 19%bv eq_refl); exact R19).
assert (E27 : ew E 27 = w64 fab) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
assert (E3a : ew E 3 = getr (lc_regs cx) 3) by (rewrite (ER 3%nat 3%bv eq_refl); exact G3).
assert (E4a : ew E 4 = getr (lc_regs cx) 4) by (rewrite (ER 4%nat 4%bv eq_refl); exact G4).
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & MOK & HNEED & HTR).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARc & Hlyc & _).
assert (ESPc : spZ (ms_regs ms) = lsp0 cx + (lsp1 cx - lsp0 cx)).
{ unfold spZ. rewrite CR2, E2a. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (ES0c : s0Z (ms_regs ms) = lsp0 cx).
{ unfold s0Z. rewrite CR8, E8a. unfold w64. apply unsigned_lit_small. lia. }
pose proof (cw_saved_keep cx fp W3 r ms3 ms KA ltac:(lia) HSAVED) as HSAVEDm.
pose proof HSAVEDm as (HRA8 & HSJ).
pose proof (HSJ 0 ltac:(lia)) as HS016. cbn [Z.ltb Z.compare] in HS016.
replace (lsp0 cx - 16 - 8 * 0) with (lsp0 cx - 16) in HS016 by lia.
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (lsp0 cx + (lsp1 cx - lsp0 cx)) (s0Z (ms_regs ms)) (lch cx)).
{ replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia.
{ rewrite ES0c. apply (cw_achain_ly (lc_ly cx)); [exact (cw_layout_top _ _ _ Hlyc)|].
  apply (lx_achain cx _ (lsp1 cx)); [exact Hch | lia | lia | apply cw_mod8; exact Hal16 | exact Hra4
    | intros a Ha; exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha)
    | unfold lview in HRA8; exact HRA8 | unfold lview in HS016; exact HS016 | lia]. } }
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs ms) (ms_mem ms) _ LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx)
    (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 _ k RANGE_FREE_STKB [] 0 (lsp1 cx - lsp0 cx) _ (lch cx)
    (fun ly' S' W' (regs' : bvmap 5 word) mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
       ((range_free_c.range_free_ok bs b nch fab /\ getr regs' 10 = w64 1) \/
        (~ range_free_c.range_free_ok bs b nch fab /\ getr regs' 10 = w64 0))) HJ).
  - exact ESPc.
  - pose proof (proj1 (Z.mod_divide (lsp1 cx) 32 ltac:(lia)) Hsp1al) as [q1 Hq1].
    pose proof (proj1 (Z.mod_divide (lsp0 cx) 16 ltac:(lia)) Hsp0al) as [q2 Hq2].
    rewrite Hq1, Hq2. replace (q1 * 32 - q2 * 16) with ((2 * q1 - q2) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold RANGE_FREE_STKB, ESTACK. lia.
  - unfold RANGE_FREE_STKB, ESTACK, LX_STK. lia.
  - rewrite CR3, E3a. exact Hgp.
  - rewrite CR4, E4a. exact Htp.
  - reflexivity.
  - rewrite CR1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite CR1. pose proof pa_base_lo. pose proof (pa_B_ok (L := boxb_listing)) as (HB0 & HB1b & _).
    rewrite unsigned_lit_small by lia. lia.
  - exact HCH.
  - intros HPREc.
    exact (RF ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (lch cx) (lF cx fp + 64) b nch fab bs HPREc
      ltac:(rewrite CR10, E21; reflexivity) ltac:(rewrite CR11, E19; reflexivity)
      ltac:(rewrite CR12, E48; reflexivity) ltac:(rewrite CR13, E27; reflexivity)
      ltac:(lia) ltac:(lia) ltac:(rewrite <- HFAB; lia) HOBJ HLEN
      ltac:(intros j Hj; exact (cw_prev_keep cx fp W3 r ms3 ms KA bs HPREV j Hj))
      HB1' HB2' HB3).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }

cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & HK).
destruct HK as (-> & -> & -> & HRES).
rewrite CR1.
pose proof HJc as (HARc2 & _ & _ & _ & _ & _ & _ & _ & FK1 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (KC : cw_kept cx fp W3 r (ms_mem ms) mem2).
{ apply cw_kept_lx.
  eapply (lx_keep_call B MT LAWS cx fp W3 ms ly3 S3 _ k HB HJ HFR [(r, LX_REG)] RANGE_FREE_STKB).
  - lia.
  - intros pp nn Hin. rewrite HBLK. apply in_or_app. left. exact Hin.
  - apply Forall_cons; [|apply Forall_nil]. exists LX_REG. cbn [fst snd].
    split; [rewrite HBLK; apply in_or_app; right; left; reflexivity|].
    pose proof (req_size_pos LX_REG ltac:(unfold LX_REG; lia)) as [_ Hq]. unfold LX_REG in *. lia.
  - replace (lsp1 cx) with (lsp0 cx + (lsp1 cx - lsp0 cx)) by lia. exact HJc. }
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W3) mem2) HP [0;1]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS2 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val CW_R20];
    rewrite UB9; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply FK1; lia.
    + intros _. apply (apresent_writable SEGS). apply Hpres2. unfold LX_STK. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val CW_R50];
    rewrite UB9; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply FK1; lia.
    + lia. }
rewrite <- restrict_mkst_fx in HS2.
cbn [app] in HJ2. replace (k + 0) with k in HJ2 by lia.
clear HS HJ SHOK. rename HS2 into HS, HJ2 into HJ.

assert (UB9c : bv_unsigned (ew (havoc E 512 (map (getr regs2) CLOB)) 9) = lsp1 cx)
  by (rewrite YN3v.ew_havoc_old by lia; exact UB9).
pose proof (img_env_havoc_hi E 512%nat (map (getr regs2) CLOB) HEI ltac:(cbv; lia)) as HEIc.
assert (SHOKc : sh_ok SEGS CW_BX [] (havoc E 512 (map (getr regs2) CLOB))
  (mrestrict (w_H W3) mem2)) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOKc CW_BSPAN.
1: { cbn [ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (lsp1 cx - lsp0 cx));
    [reflexivity | rewrite UB9c; lia | cbn; unfold LX_STK; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
cw_kd cx fp W3 r (havoc E 512 (map (getr regs2) CLOB)) GEO UB9c KB.
clear HF HFr HG HEI0.
assert (A516 : sv_denot (havoc E 512 (map (getr regs2) CLOB)) (SOff 516 0) = getr regs2 10)
  by exact (cw_denot_a0 E 512 regs2).
psrr_branch_tok RUN BR HS SHOKc CW_BSPAN.
all: rewrite A516 in Hc.
all: destruct HRES as [(HOKb & HA0) | (HOKb & HA0)]; rewrite HA0 in Hc; cbn [branch_taken] in Hc;
  try (vm_compute in Hc; discriminate Hc); clear Hc.

1: { paj_run_to_tok RUNTO HS HJ SHOKc CW_BSPAN C1_P7.
  1: { cbn [ss_mem add_cond].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (lsp1 cx - lsp0 cx));
      [reflexivity | rewrite UB9c; lia | cbn; unfold LX_STK; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  cw_kd cx fp W3 r (havoc E 512 (map (getr regs2) CLOB)) GEO UB9c KD.
  clear HF HFr HG HEI0.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (KALL : cw_kept cx fp W3 r (ms_mem ms3) (ms_mem msx)) end.
  { eapply cw_kept_trans; [exact KA|]. eapply cw_kept_trans; [exact KC|].
    eapply cw_kept_trans; [exact KB | exact KD]. }
  (* the slot lf now holds b *)
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (SLB : rdword (aview SEGS (w_H W3) (ms_mem msx)) (lsp1 cx + 0x20) = Some b) end.
  { apply (lx_word_of_ss W3 _ (havoc E 512 (map (getr regs2) CLOB)) _ 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32
      (SOff 19 0) b HS eq_refl UB9c ltac:(left; reflexivity)); [|lia].
    cbn [sv_denot]. rewrite YN3v.ew_havoc_old by lia. rewrite E19. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  pmkst HS.
  assert (F2 : ew (havoc E 512 (map (getr regs2) CLOB)) 2 = w64 (lsp1 cx)) by (rewrite YN3v.ew_havoc_old by lia; exact E2a).
  assert (F8 : ew (havoc E 512 (map (getr regs2) CLOB)) 8 = w64 (lsp0 cx)) by (rewrite YN3v.ew_havoc_old by lia; exact E8a).
  assert (F9 : ew (havoc E 512 (map (getr regs2) CLOB)) 9 = w64 (lsp1 cx)) by (rewrite YN3v.ew_havoc_old by lia; exact E9).
  assert (F3 : ew (havoc E 512 (map (getr regs2) CLOB)) 3 = getr (lc_regs cx) 3) by (rewrite YN3v.ew_havoc_old by lia; exact E3a).
  assert (F4 : ew (havoc E 512 (map (getr regs2) CLOB)) 4 = getr (lc_regs cx) 4) by (rewrite YN3v.ew_havoc_old by lia; exact E4a).
  assert (F18 : ew (havoc E 512 (map (getr regs2) CLOB)) 18 = w64 SHADOW_OFF)
    by (rewrite YN3v.ew_havoc_old by lia; rewrite (ER 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew (havoc E 512 (map (getr regs2) CLOB)) 22 = w64 (lSH cx fp))
    by (rewrite YN3v.ew_havoc_old by lia; rewrite (ER 22%nat 22%bv eq_refl); exact G22).
  assert (F20 : ew (havoc E 512 (map (getr regs2) CLOB)) 20 = w64 r)
    by (rewrite YN3v.ew_havoc_old by lia; rewrite (ER 20%nat 20%bv eq_refl); exact R20).
  assert (F21 : ew (havoc E 512 (map (getr regs2) CLOB)) 21 = w64 (lF cx fp + 64)) by (rewrite YN3v.ew_havoc_old by lia; exact E21).
  assert (F23 : ew (havoc E 512 (map (getr regs2) CLOB)) 23 = w64 w7)
    by (rewrite YN3v.ew_havoc_old by lia; rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (F26 : ew (havoc E 512 (map (getr regs2) CLOB)) 26 = w64 (Boxreg.bx_n bs))
    by (rewrite YN3v.ew_havoc_old by lia; rewrite (ER 26%nat 26%bv eq_refl); exact R26).
  assert (F27 : ew (havoc E 512 (map (getr regs2) CLOB)) 27 = w64 fab) by (rewrite YN3v.ew_havoc_old by lia; exact E27).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  apply (cw_to7 POST i cx fp k acc ly3 S3 W3 ms3 _ _ _ q r fab bs M nch nz b (Boxreg.bx_n bs)
    w7 C1_P6 HN7 HB HJ HFR HMO HBODY1 HREAD HNZ KALL);
  [ rewrite Z.mod_small by lia; exact SLB
  | lia
  | right; right; right; right; rewrite HFAB; split; [exact Hok|]; split; [exact HM0|]; split; [exact Hnh|];
    split; [exact Hnu|]; split; [exact Hn5|]; split; [reflexivity|]; split; [lia|];
    exact (lxc1_lf_hit bs nch fab b Hlfi HOKb)
  | lia | exact Hw7 | split; [intros _; exact Hok | intros _; exact Hw70]
  | cw_reg_close ER .. ]. }

assert (ER24 : ew E 24 = w64 (fab - nch + 1)) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
paj_run_tok RUN HS HJ SHOKc CW_BSPAN.
1: { cbn [ss_mem add_cond].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (lsp1 cx - lsp0 cx));
    [reflexivity | rewrite UB9c; lia | cbn; unfold LX_STK; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
cw_kd cx fp W3 r (havoc E 512 (map (getr regs2) CLOB)) GEO UB9c KE.
clear HF HFr HG HEI0.
psrr_branch_tok RUN BR HS SHOKc CW_BSPAN.
all: rewrite (cw_br_ne _ (SOff 24 0) (SAluw ALU_ADD (SOff 19 0) (SLit 1)) (fab - nch + 1) (b + 1)) in Hc;
  [ | apply cw_atom0; [rewrite YN3v.ew_havoc_old by lia; exact ER24 | lia]
    | apply (cw_addw _ _ _ b 1); [apply cw_atom0; [rewrite YN3v.ew_havoc_old by lia; exact E19 | lia]
        | reflexivity | lia | lia | lia]
    | lia | lia ].

1: { paj_run_to_tok RUNTO HS HJ SHOKc CW_BSPAN C1_P6.
  1: { cbn [ss_mem add_cond].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (lsp1 cx - lsp0 cx));
      [reflexivity | rewrite UB9c; lia | cbn; unfold LX_STK; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  cw_kd cx fp W3 r (havoc E 512 (map (getr regs2) CLOB)) GEO UB9c KD.
  clear HF HFr HG HEI0.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (KALL : cw_kept cx fp W3 r (ms_mem ms3) (ms_mem msx)) end.
  { eapply cw_kept_trans; [exact KA|]. eapply cw_kept_trans; [exact KC|].
    eapply cw_kept_trans; [exact KB|]. eapply cw_kept_trans; [exact KE | exact KD]. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (SLB : rdword (aview SEGS (w_H W3) (ms_mem msx)) (lsp1 cx + 0x20) = Some (2 ^ 64 - 1)) end.
  { apply (lx_word_of_ss W3 _ (havoc E 512 (map (getr regs2) CLOB)) _ 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32
      (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) HS eq_refl UB9c ltac:(left; reflexivity)); [reflexivity | lia]. }
  pmkst HS.
  cw_rawreg HS (19%bv : bv 5) Q19.
  rewrite (cw_addw _ _ _ b 1) in Q19;
    [ | apply cw_atom0; [rewrite YN3v.ew_havoc_old by lia; exact E19 | lia] | reflexivity | lia | lia | lia].
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  apply (IHn cx fp k acc ly3 S3 W3 _ _ q r fab bs M nch nz (b + 1) w7);
  [ apply Nat.lt_succ_r; apply Nat2Z.inj_lt; rewrite !Z2Nat.id by lia; lia
  | exact HB | exact HJ | exact HFR | exact HMO |].
  apply (cw_to6 i cx fp k acc ly3 S3 W3 ms3 _ _ q r fab bs M nch nz (b + 1) w7 C1_P6
    HB HBODY1 HREAD HNZ KALL);
  [ exact SLB | exact Hok | exact HM0 | exact Hnh | exact Hnu | exact Hn5
  | exact (lxc1_lf_step bs nch fab b Hlfi HOKb)
  | apply negb_true_iff in Hc; apply Z.eqb_neq in Hc; lia
  | exact Hw7 | exact Hw70
  | cw_reg_close ER .. ]. }

(* b + 1 = fab - nch + 1: no base is free; 0x809a4 s9 = -1 *)
apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
paj_run_to_tok RUNTO HS HJ SHOKc CW_BSPAN C1_P7.
1: { cbn [ss_mem add_cond].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (lsp1 cx - lsp0 cx));
    [reflexivity | rewrite UB9c; lia | cbn; unfold LX_STK; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
cw_kd cx fp W3 r (havoc E 512 (map (getr regs2) CLOB)) GEO UB9c KD.
clear HF HFr HG HEI0.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (KALL : cw_kept cx fp W3 r (ms_mem ms3) (ms_mem msx)) end.
{ eapply cw_kept_trans; [exact KA|]. eapply cw_kept_trans; [exact KC|].
  eapply cw_kept_trans; [exact KB|]. eapply cw_kept_trans; [exact KE | exact KD]. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (SLB : rdword (aview SEGS (w_H W3) (ms_mem msx)) (lsp1 cx + 0x20) = Some (2 ^ 64 - 1)) end.
{ apply (lx_word_of_ss W3 _ (havoc E 512 (map (getr regs2) CLOB)) _ 0%nat 9%nat (lsp1 cx) 32 40 32 40 _ 32
    (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) HS eq_refl UB9c ltac:(left; reflexivity)); [reflexivity | lia]. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
apply (cw_to7 POST i cx fp k acc ly3 S3 W3 ms3 _ _ _ q r fab bs M nch nz (-1) (-1)
  w7 C1_P6 HN7 HB HJ HFR HMO HBODY1 HREAD HNZ KALL);
[ replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity; exact SLB
| lia
| right; right; right; left; rewrite HFAB; split; [exact Hok|]; split; [exact HM0|]; split; [exact Hnh|];
  split; [exact Hnu|]; split; [|reflexivity]; right;
  exact (lxc1_lf_miss bs nch fab (b + 1) (lxc1_lf_step bs nch fab b Hlfi HOKb) ltac:(lia))
| lia | exact Hw7 | split; [intros _; exact Hok | intros _; exact Hw70]
| cw_reg_close ER .. ].
Qed.

Theorem c1_seg_lf : C1_SEG_lf B MT.
Proof.
intros HY POST i HN7 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (q & r & fab & bs & M & nch & nz & b & w7 & HI6).
exact (cw_lf_n POST i HY HN7 (Z.to_nat (fab - nch + 1 - b)) cx fp k acc ly3 S3 W3 ms3 md3
         q r fab bs M nch nz b w7 (Nat.le_refl _) HB HJ HFR HMO HI6).
Qed.

End c.
End b.
End a.
