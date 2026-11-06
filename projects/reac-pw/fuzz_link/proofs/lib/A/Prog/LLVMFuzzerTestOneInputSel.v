(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 243 of its 306 lines of code are new or changed and 341 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the name selector the arms op_read, op_write and op_mark share (a
   ruling: one shape for the three arms). Each arm reads the byte after the operation byte
   and picks a name:
     no byte left (N = 0)       g_names + 8 * 0
     byte 0xff                  0 (no name)
     byte sel <= 0x3f           g_names + 8 * sel
     byte sel > 0x3f            odd[sel mod 6], read through the LS_ODD slot (an instrumented 8-byte load)
   This file holds what the arms' runs share: the name as a memory-free fact (`w_name s nm`, with the odd table's
   six words by computation, ODD_PTRS), the image checks, and the symbolic pieces (the mulhu-based sel mod 6 and
   the regions of the odd word).

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YFen.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   The name, memory-free
   ========================================================================== *)
Definition ODD_PTRS : list Z := map fst KP_ODD.

Definition w_name (s : Z) (nm : option (list byte)) : Prop :=
  (s = 0 /\ nm = None) \/
  (exists k, 0 <= k < 64 /\ s = LA_G_NAMES + 8 * k /\ nm = Some (lf_gname k)) \/
  (exists j, (j < 6)%nat /\ s = nth j ODD_PTRS 0 /\ nm = Some (nth j lf_odd_strs [])).

(* the odd strings are KP_ODD's bytes *)
Lemma sel_odd_strs : forall j, (j < 6)%nat -> nth j lf_odd_strs [] = map (Z_to_bv 8) (snd (nth j KP_ODD (0, []))).
Proof.
  intros j Hj. do 6 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

(* the image: the odd table's six words and strings, the odd table's and g_names' shadow *)
Definition sel_img_b (segs : list Segment) (own : list (Z * Z)) (err : Z) : bool :=
  forallb (fun i => let e := nth i KP_ODD (0, []) in
     kp_bytes_b segs own err (LA_ODD + 8 * Z.of_nat i) (kp_le8 (fst e)) && kp_kstr_b segs own err (fst e) (snd e))
    (seq 0 6)
  && kp_ra_b LA_ODD 48 && kp_ra_b LA_G_NAMES G_NAMES_SIZE && kp_hull_b LA_G_NAMES G_NAMES_SIZE.
Lemma sel_img_checks : sel_img_b tfibsegs Tfib_owned_static TFIB_ERRNO = true.
Proof. vm_compute. reflexivity. Qed.

(* sel mod 6 the arms compute: a1 := mulhu sel 0x2aaaaaaaaaaaaaab (sel / 6), a0 := sel - 6 * a1 *)
Definition sel_c6 : Z := 0x2aaaaaaaaaaaaaab.
Lemma sel_mulhu_all : forallb (fun b => Z.eqb ((b * sel_c6) / 2 ^ 64) (b / 6)) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sel_mulhu : forall b, 0 <= b < 256 -> (b * sel_c6) / 2 ^ 64 = b / 6.
Proof.
  intros b Hb. pose proof sel_mulhu_all as H. rewrite forallb_forall in H.
  specialize (H b ltac:(apply in_map_iff; exists (Z.to_nat b); split; [lia | apply in_seq; lia])).
  apply Z.eqb_eq in H. exact H.
Qed.

(* ==========================================================================
   The selector's symbolic pieces (the same instruction words at op_read, op_write and op_mark)
   ========================================================================== *)
(* the constant 0x2aaaaaaaaaaaaaab at .rodata + 0xa0 (0x10380), loaded by `auipc a1; ld a1, -0x414(a1)` *)
Definition w_c6_rg : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 11)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit sel_c6))].
Lemma w_c6_checks : link_obj 11 = 0x10380 /\
  kp_bytes_b tfibsegs Tfib_owned_static TFIB_ERRNO 0x10380 (kp_le8 sel_c6) = true.
Proof. split; vm_compute; reflexivity. Qed.
(* +0xfc0 .. +0xfe4: a0 := LA_ODD + ((b - 6 * mulhu(b, 0x2aaaaaaaaaaaaaab)) << 3) *)
Definition w_mh : sv := SMd M_MULHU (SOff 34 0) (SLit 3074457345618258603).
Definition w_a0 : sv :=
  SAlu ALU_ADD (SOff 35 0)
    (SAlu ALU_SLL (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SUB (SAlu ALU_SLL w_mh (SLit 1)) (SAlu ALU_SLL w_mh (SLit 3))))
       (SLit 3)).
Definition w_Eb (b : Z) : env := mkEnv (fun n => if Nat.eqb n 35 then Z_to_bv 64 LA_ODD else Z_to_bv 64 b) (fun _ => []).
Lemma w_a0_all : forallb (fun b => Z.eqb (bv_unsigned (sv_denot (w_Eb b) w_a0)) (LA_ODD + 8 * (b mod 6)))
  (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w_a0_val : forall E b, ew E 34 = Z_to_bv 64 b -> ew E 35 = Z_to_bv 64 LA_ODD -> 0 <= b < 256 ->
  sv_denot E w_a0 = Z_to_bv 64 (LA_ODD + 8 * (b mod 6)).
Proof.
  intros E b H34 H35 Hb.
  rewrite (YFen.sv_denot_agree_on (fun n => (Nat.eqb n 34 || Nat.eqb n 35)%bool) (w_Eb b) E w_a0);
    [| intros n Hn; apply Bool.orb_true_iff in Hn as [Hn | Hn]; apply Nat.eqb_eq in Hn; subst n;
         [exact H34 | exact H35] | reflexivity].
  pose proof (proj1 (forallb_forall _ _) w_a0_all b ltac:(apply in_map_iff; exists (Z.to_nat b);
    split; [apply Z2Nat.id; lia | apply in_seq; lia])) as H. apply Z.eqb_eq in H.
  apply bv_eq. rewrite H, unsigned_lit_small by (pose proof (Z.mod_pos_bound b 6); unfold LA_ODD; lia). reflexivity.
Qed.
(* the odd table's word k, on the atom that holds LA_ODD *)
Definition w_odd_tab (k : Z) : YP09.region :=
  YP09.mkRegion (Some 35%nat) (8 * k) (8 * k + 8) 0 0 [YP09.mkChunk (8 * k) (CVal 8 (SLit (nth (Z.to_nat k) ODD_PTRS 0)))].
(* +0xa7c .. +0xa88: s5 := g_names + (b << 3), g_names through the auipc / addi pair (object atom 246 = A_OBJ 5) *)
Definition w_gn : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 3)) (SOff 246 0).
Definition w_Eg (b : Z) : env :=
  mkEnv (fun n => if Nat.eqb n 246 then Z_to_bv 64 LA_G_NAMES else Z_to_bv 64 b) (fun _ => []).
Lemma w_gn_all : forallb (fun b => Z.eqb (bv_unsigned (sv_denot (w_Eg b) w_gn)) (LA_G_NAMES + 8 * b))
  (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w_gn_val : forall E b, ew E 34 = Z_to_bv 64 b -> ew E 246 = Z_to_bv 64 LA_G_NAMES -> 0 <= b < 256 ->
  sv_denot E w_gn = Z_to_bv 64 (LA_G_NAMES + 8 * b).
Proof.
  intros E b H34 H246 Hb.
  rewrite (YFen.sv_denot_agree_on (fun n => (Nat.eqb n 34 || Nat.eqb n 246)%bool) (w_Eg b) E w_gn);
    [| intros n Hn; apply Bool.orb_true_iff in Hn as [Hn | Hn]; apply Nat.eqb_eq in Hn; subst n;
         [exact H34 | exact H246] | reflexivity].
  pose proof (proj1 (forallb_forall _ _) w_gn_all b ltac:(apply in_map_iff; exists (Z.to_nat b);
    split; [apply Z2Nat.id; lia | apply in_seq; lia])) as H. apply Z.eqb_eq in H.
  apply bv_eq. rewrite H, unsigned_lit_small by (unfold LA_G_NAMES; lia). reflexivity.
Qed.
Lemma w_obj5 : link_obj 5 = LA_G_NAMES.
Proof. vm_compute. reflexivity. Qed.
Lemma w_odd_ptrs : ODD_PTRS = [135104; 135136; 135168; 135200; 135232; 135264].
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

Lemma sel_img_here : sel_img_b SEGS (as_owned_static B) (as_errno B) = true.
Proof. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB). exact sel_img_checks. Qed.

(* the odd word of entry j at any memory the read-only image pins *)
Lemma sel_odd_word : forall (W : world SEGS) mem j v,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) -> (j < 6)%nat ->
  au64_at SEGS (rdW W mem) (LA_ODD + 8 * Z.of_nat j) v -> 0 <= v < 2 ^ 64 -> v = nth j ODD_PTRS 0.
Proof.
  intros W mem j v HRO Hj Hv Rv.
  pose proof sel_img_here as KI. unfold sel_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  pose proof (kp_forallb_seq _ _ KI j Hj) as Hx. cbv beta zeta in Hx. apply andb_prop in Hx as [Hw Hs].
  pose proof (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ eq_refl eq_refl HRO Hw) as Ve.
  pose proof (kp_vm8_mod _ _ _ _ _ Hv Ve) as E.
  destruct (kp_kstr_acstr B (w_H W) mem _ _ HRO Hs) as (_ & Hq0 & Hql). unfold LA_G_NL in Hql.
  unfold ODD_PTRS. rewrite (map_nth fst KP_ODD (0, [])) .
  rewrite !Z.mod_small in E by lia. exact E.
Qed.

(* the odd word as a chunk of a region based at the atom that holds LA_ODD *)
Lemma sel_odd_val : forall (W : world SEGS) mem j,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) -> (j < 6)%nat ->
  val_mem SEGS (rdW W mem) (LA_ODD + 8 * Z.of_nat j) 8 (nth j ODD_PTRS 0) /\ 0 < nth j ODD_PTRS 0 < 2 ^ 47.
Proof.
  intros W mem j HRO Hj.
  pose proof sel_img_here as KI. unfold sel_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  pose proof (kp_forallb_seq _ _ KI j Hj) as Hx. cbv beta zeta in Hx. apply andb_prop in Hx as [Hw Hs].
  unfold ODD_PTRS. rewrite (map_nth fst KP_ODD (0, [])).
  split; [exact (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ eq_refl eq_refl HRO Hw)|].
  do 6 (destruct j as [|j]; [vm_compute; split; reflexivity|]). lia.
Qed.

(* the odd table's 48 bytes are addressable at every AR state *)
Lemma sel_odd_ra : forall ly S rd, ARm B ly S rd -> range_addressable rd SHADOW_OFF LA_ODD 48.
Proof.
  intros ly S rd M. pose proof sel_img_here as KI. unfold sel_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with H : kp_ra_b LA_ODD 48 = true |- _ => exact (kp_ra B TB ly S rd _ _ M H) end.
Qed.

(* g_names' 512 bytes: addressable, and their shadow visible *)
Lemma sel_gnames_ra : forall ly S rd, ARm B ly S rd ->
  range_addressable rd SHADOW_OFF LA_G_NAMES G_NAMES_SIZE /\ shadow_hull_vis rd LA_G_NAMES G_NAMES_SIZE.
Proof.
  intros ly S rd M. pose proof sel_img_here as KI. unfold sel_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  split.
  - match goal with H : kp_ra_b LA_G_NAMES G_NAMES_SIZE = true |- _ => exact (kp_ra B TB ly S rd _ _ M H) end.
  - match goal with H : kp_hull_b LA_G_NAMES G_NAMES_SIZE = true |- _ => exact (kp_hull B TB ly S rd _ _ M H) end.
Qed.

End a.

(* ==========================================================================
   The join: the arm at the point where the three selector paths meet, the name in register rn
   (op_write: s5 = 21; op_read: s6 = 22)
   ========================================================================== *)
(* ==========================================================================
   The selector's image atoms and regions (the instance's LinkVals)
   ========================================================================== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis LV : LinkVals (PI := PI).

Lemma w_atom346 : forall E, img_env pa_val A_LIM E -> bv_unsigned (ew E (A_OBJ 11)) = 0x10380.
Proof.
  intros E HE. rewrite (HE (A_OBJ 11) ltac:(split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity)).
  rewrite (lv_obj LV 11 ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  exact (proj1 w_c6_checks).
Qed.

Lemma w_atom246 : forall E, img_env pa_val A_LIM E -> ew E 246 = Z_to_bv 64 LA_G_NAMES.
Proof.
  intros E HE. apply bv_eq. rewrite unsigned_lit_small by (unfold LA_G_NAMES; lia).
  change 246%nat with (A_OBJ 5).
  rewrite (HE (A_OBJ 5) ltac:(split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity)).
  rewrite (lv_obj LV 5 ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). exact w_obj5.
Qed.

Lemma w_c6_ok : forall E (W : world SEGS) mem, img_env pa_val A_LIM E ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  YP09.region_ok SEGS E (rdW W mem) w_c6_rg.
Proof.
  intros E W mem HE HR. unfold YP09.region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks w_c6_rg base_val].
  rewrite (w_atom346 E HE). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ 0x10380 0 8 (SLit sel_c6) sel_c6);
    [reflexivity | cbn; unfold sel_c6; lia | cbn; lia |].
  rewrite Z.add_0_r.
  apply (kp_val_mem8 SEGS Tfib_owned_static TFIB_ERRNO B (w_H W) mem _ _ (ts_owned B TB) (ts_errno B TB) HR).
  rewrite HSEGS. exact (proj2 w_c6_checks).
Qed.

Lemma w_odd_tab_ok : forall E (W : world SEGS) mem k, ew E 35 = Z_to_bv 64 LA_ODD ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) -> 0 <= k < 6 ->
  YP09.region_ok SEGS E (rdW W mem) (w_odd_tab k).
Proof.
  intros E W mem k H35 HR Hk. unfold YP09.region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks w_odd_tab base_val].
  rewrite H35, unsigned_lit_small by (unfold LA_ODD; lia).
  destruct (sel_odd_val B TB HSEGS W mem (Z.to_nat k) HR ltac:(lia)) as (Hv & Hq).
  split; [unfold LA_ODD; lia|]. split; [unfold LA_ODD; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ LA_ODD (8 * k) 8 (SLit (nth (Z.to_nat k) ODD_PTRS 0)) (nth (Z.to_nat k) ODD_PTRS 0));
    [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
  rewrite Z2Nat.id in Hv by lia. exact Hv.
Qed.

Lemma w_k6 : forall b, 0 <= b < 256 -> exists k, In k [0; 1; 2; 3; 4; 5] /\ b mod 6 = k.
Proof.
  intros b Hb. exists (b mod 6). split; [|reflexivity].
  pose proof (Z.mod_pos_bound b 6 ltac:(lia)).
  assert (b mod 6 = 0 \/ b mod 6 = 1 \/ b mod 6 = 2 \/ b mod 6 = 3 \/ b mod 6 = 4 \/ b mod 6 = 5) as Hc by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; cbn; tauto.
Qed.

End w.

Ltac sel_inbv := cbn [In]; repeat (first [left; reflexivity | right]).

Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws pa_segs B.
#[local] Notation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* lf_lregs but at the name's register *)
Definition sel_lregs (rn : bv 5) (cx : lcx) (md fp i : Z) (ms3 : machine_state) : Prop :=
  (rn = 19%bv \/ getr (ms_regs ms3) 19 = w64 (lf_SH cx fp)) /\
  (rn = 21%bv \/ getr (ms_regs ms3) 21 = w64 (md + MD_N_MARK)) /\
  (rn = 22%bv \/ getr (ms_regs ms3) 22 = w64 md) /\
  getr (ms_regs ms3) 23 = w64 (LA_G_NL + 0x40000) /\
  getr (ms_regs ms3) 24 = w64 (2 ^ 64 - 8) /\
  getr (ms_regs ms3) 25 = w64 i /\
  getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  getr (ms_regs ms3) 27 = w64 SHADOW_OFF.

Definition sel_join (pcj : Z) (rn : bv 5) (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout)
    (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (nm : option (list byte)) (kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  0 <= i <= 47 /\ lf_shape fy pcj ms3 /\ lf_core cx ms3 /\ sel_lregs rn cx md fp i ms3 /\
  getr (ms_regs ms3) rn = w64 s /\ w_name s nm /\
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 [(md, MD_SIZE); (mk, MK_SIZE)]
    (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD k2 ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\ nk_opened kbs <= 64 * i.

Lemma sel_bv_ne : forall a b : bv 5, bv_unsigned a <> bv_unsigned b -> a <> b.
Proof. intros a b H E. subst. exact (H eq_refl). Qed.

(* the join from a run's end state: the cut's memory clauses kept off the cursor's two words *)
Lemma sel_close : forall pcj (rn : bv 5) i cx (fy : YK11.FPState) fp k2 ly3 S3 W3 ms3 md3 msB md4 md mk P' N' s nm
    kbs mbs gbs T3,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] -> 0 <= i <= 47 ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 -> lf_slots cx md mk fp W3 ms3 ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) -> nk_opened kbs <= 64 * i ->
  lf_core cx ms3 -> lf_lregs cx md fp i ms3 ->
  JRN cx fp ly3 S3 W3 (ms_mem msB) md4 k2 -> lf_shape fy pcj msB ->
  (rn = 19%bv \/ rn = 21%bv \/ rn = 22%bv) ->
  (forall r : bv 5, In r [2%bv; 8%bv; 9%bv; 3%bv; 4%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
     r <> rn -> getr (ms_regs msB) r = getr (ms_regs ms3) r) ->
  getr (ms_regs msB) rn = w64 s -> w_name s nm ->
  kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
    (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  lf_cur cx W3 msB P' N' ->
  sel_join pcj rn i cx fy fp k2 ly3 S3 W3 msB md4.
Proof.
  intros pcj rn i cx fy fp k2 ly3 S3 W3 ms3 md3 msB md4 md mk P' N' s nm kbs mbs gbs T3
    HB HJ Hfr Hi Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hop Hcore Hlr HJB Hsh Hrn KR Hs Hnm KBm GBm Fd Fs Hcur.
  pose proof (lf_sp1_le cx) as (P1 & P2).
  assert (XN : forall a, lf_cut_fp MS la_nul cx fp md mk T3 a ->
            ~ (lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)).
  { intros a Ha. assert (HFR : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
    pose proof asan_consts as ((C1a & C1b) & _).
    destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
      (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & Hs47 & _ & _).
    assert (Hs1 : spZ (c_regs cx) - LF_MFRAME - 16 <= lf_sp1 cx).
    { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
        as (R & _). lia. }
    destruct (lf_cut_fp_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp k2
      ly3 S3 W3 (ms_mem ms3) md3 _ _ _ _ ms3 md3 md mk T3 _ a HB HJ HFR Hjbk Hblk Ha) as [Hp | [Hp | Hp]];
      rewrite Z.mod_small by (unfold LF_MFRAME, LLVMF_STK in *; lia); unfold LS_P, LS_N, LF_MFRAME, LLVMF_STK in *; lia. }
  destruct (lf_cut_keep B MT MS la_nul _ cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ ly3 S3 W3 ms3 md3
    W3 msB md4 KBm (wcarry_on_grows _ _ _ GBm) Fd Fs XN Hsv Hhd Hfs Hsl Hjbk Hblk Hdat)
    as (Hsv' & Hhd' & Hfs' & Hsl' & Hjbk' & Hblk' & Hdat').
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  exists md, mk, P', N', s, nm, kbs, mbs, gbs, T3.
  split; [exact Hi|]. split; [exact Hsh|].
  destruct Hrn as [-> | [-> | ->]];
    (split; [unfold lf_core; rewrite !KR by (first [solve [sel_inbv] | apply sel_bv_ne; vm_compute; intros Habs; discriminate Habs]); repeat split; assumption|]);
    (split; [unfold sel_lregs;
             repeat split; first [left; reflexivity | right; rewrite KR by (first [solve [sel_inbv] | apply sel_bv_ne; vm_compute; intros Habs; discriminate Habs]);
                                  assumption | rewrite KR by (first [solve [sel_inbv] | apply sel_bv_ne; vm_compute; intros Habs; discriminate Habs]); assumption]|]);
    (split; [exact Hs|]); (split; [exact Hnm|]);
    (split; [|split; [exact Hcur | exact Hop]]);
    (split; [exact HJB|]); (split; [exact Hfr|]); (split; [exact Hsv'|]); (split; [exact Hhd'|]);
    (split; [exact Hfs'|]); (split; [exact Hsl'|]); (split; [exact Hjbk'|]); (split; [exact Hblk' | exact Hdat']).
Qed.

End j.

