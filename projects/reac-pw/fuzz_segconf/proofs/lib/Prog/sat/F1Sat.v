(** reac-pw/fuzz_segconf, plain build (image 3776ca44d75c): satisfiability of the premises of contract family F1.
    For each of the 18 contracts (lib/Prog/*_c.v; the text of commit e3c794acbc3d, unchanged through c7b9518dac31,
    which this tree is on) one
    closed lemma [<fn>_pre_sat]: its named premise holds at a real call site with real values. The lemmas with a
    suffix ([_absent], [_nosuch], [_acc_absent], [_acc_nosuch], [_dropin]) cover the function's other callers, so
    that every call site of the 18 functions has its lemma.

    proves no function (kind: statement text; closed satisfiability lemmas of contract premises). Nothing here is an
    Axiom, a Parameter, an admit or an Admitted.

    The real values (Prog/SegSatKit.v section 4): the input D0 = [4; 1; 0; 0; 64; 0] ++ T0, whose decode is the
    payload with cap 4, flags 1 and one file T0 =
      "[segment eth0.5]\nrole = box\nmodel = s1608\nignore = no\nknock = 1\n";
    the reader's state RC0 = fst (r_parse rconf0 T0) and the model's MC0 = m_cross (m_file mconf0 T0 None)
    (SegSatKit.run_P0: they are run's; SegSatKit.harness_ok_P0: no check aborts on this input); the segment
    m->seg[0] = G0, its name NM0 = "eth0.5", the probe PROBE0 = "eth0.5x", "nosuch0" at seg_spec.STR_NOSUCH; the
    one refusal (the knock line: the reader's text holds "takes no plan", the model keeps "reac-pw.conf:5: " with
    kept_knock = 1); the VLAN tables GOT0 / WANT0 = r_declared / m_declared of vlan_init (both
    (1, [("enp1s0", 33); ("eth0", 5)])). The blocks c, m, tab, mt sit at the 16-aligned heap addresses C0, M0,
    TAB0, MT0 holding SegSatKit's canonical images of these states; the stack region is [LO, S_TOP) with
    LO = S_TOP - 65536, S_TOP = 0x7ffffffef000; sp at each call site is S_TOP minus the frames of its callers
    (Prog/SegSat.v). The stack-protector GOT cell (0x21818, holding 0x52e80) and the guard (0x52e80, 0) and the
    string "nosuch0" are read from the image. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec SegSatKit SegSat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import
  reac_segconf_init_c reac_segconf_find_c reac_segconf_ignored_c reac_segconf_role_c reac_segconf_role_file_c
  reac_segconf_ignore_file_c reac_segconf_model_c reac_box_catalogue_by_token_c check_segments_c check_role_c
  check_model_c check_ignore_c check_provenance_c check_refusals_c check_address_c check_knock_refused_c
  check_absent_c check_declared_c.
Import ListNotations.
Open Scope Z_scope.

Ltac sg := sat_goal rsegs_below.
Ltac sat := csplit; sg.

(** reac_segconf_init, LLVMFuzzerTestOneInput 0x138c4: c = malloc(16616) at C0, sp = main's. *)
Lemma reac_segconf_init_pre_sat : reac_segconf_init_pre (RMEM RS_INIT) SP_MAIN LO C0.
Proof.
  unfold reac_segconf_init_pre. csplit; [zside | zside | | sg | sg | sg].
  exists (zb (zrep 16616)).
  replace (Z.to_nat SEG_C_SIZE) with (length (zb (zrep 16616))) by (vm_compute; reflexivity).
  apply rw_cells_CB; sg.
Qed.

(** reac_segconf_find, from reac_segconf_ignored (frame 16) at LLVMFuzzerTestOneInput 0x13b40: name = m->seg[0].name. *)
Lemma reac_segconf_find_pre_sat :
  query_pre FIND_STACK (RMEM (RSQ R_CELL0)) (SP_MAIN - ACC_FRAME) LO C0 (mseg_addr M0 0) RC0 NM0.
Proof. unfold query_pre. sat. Qed.

(** reac_segconf_find, from check_absent 0x14a78 (frame 32): name = the probe on main's frame, and "nosuch0". *)
Lemma reac_segconf_find_pre_sat_absent :
  query_pre FIND_STACK (RMEM RSP) (SP_MAIN - ABSENT_FRAME) LO C0 OUT RC0 PROBE0.
Proof. unfold query_pre. sat. Qed.

Lemma reac_segconf_find_pre_sat_nosuch :
  query_pre FIND_STACK (RMEM RSP) (SP_MAIN - ABSENT_FRAME) LO C0 STR_NOSUCH RC0 S_nosuch.
Proof. unfold query_pre. sat. Qed.

(** reac_segconf_find, from an accessor (frame 16) that check_absent (frame 32) calls: the probe, and "nosuch0". *)
Lemma reac_segconf_find_pre_sat_acc_absent :
  query_pre FIND_STACK (RMEM RSP) (SP_MAIN - ABSENT_FRAME - ACC_FRAME) LO C0 OUT RC0 PROBE0.
Proof. unfold query_pre. sat. Qed.

Lemma reac_segconf_find_pre_sat_acc_nosuch :
  query_pre FIND_STACK (RMEM RSP) (SP_MAIN - ABSENT_FRAME - ACC_FRAME) LO C0 STR_NOSUCH RC0 S_nosuch.
Proof. unfold query_pre. sat. Qed.

(** reac_segconf_ignored, LLVMFuzzerTestOneInput 0x13b40, and check_absent 0x14a9c. *)
Lemma reac_segconf_ignored_pre_sat :
  query_pre IGNORED_STACK (RMEM (RSQ R_CELL0)) SP_MAIN LO C0 (mseg_addr M0 0) RC0 NM0.
Proof. unfold query_pre. sat. Qed.

Lemma reac_segconf_ignored_pre_sat_absent :
  query_pre IGNORED_STACK (RMEM RSP) (SP_MAIN - ABSENT_FRAME) LO C0 OUT RC0 PROBE0.
Proof. unfold query_pre. sat. Qed.

Lemma reac_segconf_ignored_pre_sat_nosuch :
  query_pre IGNORED_STACK (RMEM RSP) (SP_MAIN - ABSENT_FRAME) LO C0 STR_NOSUCH RC0 S_nosuch.
Proof. unfold query_pre. sat. Qed.

(** reac_segconf_role, LLVMFuzzerTestOneInput 0x13b14: out = &r (main's cell, 0x5a); check_absent 0x14a8c: out = NULL. *)
Lemma reac_segconf_role_pre_sat :
  role_pre (RMEM (RSQ 0x5a)) SP_MAIN LO C0 (mseg_addr M0 0) OUT RC0 NM0.
Proof. unfold role_pre, query_pre. sat. Qed.

Lemma reac_segconf_role_pre_sat_absent :
  role_pre (RMEM RSP) (SP_MAIN - ABSENT_FRAME) LO C0 OUT 0 RC0 PROBE0.
Proof. unfold role_pre, query_pre. sat. Qed.

Lemma reac_segconf_role_pre_sat_nosuch :
  role_pre (RMEM RSP) (SP_MAIN - ABSENT_FRAME) LO C0 STR_NOSUCH 0 RC0 S_nosuch.
Proof. unfold role_pre, query_pre. sat. Qed.

(** reac_segconf_role_file, LLVMFuzzerTestOneInput 0x13b54. *)
Lemma reac_segconf_role_file_pre_sat :
  query_pre ROLE_FILE_STACK (RMEM (RSQ R_CELL0)) SP_MAIN LO C0 (mseg_addr M0 0) RC0 NM0.
Proof. unfold query_pre. sat. Qed.

(** reac_segconf_ignore_file, LLVMFuzzerTestOneInput 0x13b64. *)
Lemma reac_segconf_ignore_file_pre_sat :
  query_pre IGNORE_FILE_STACK (RMEM (RSQ R_CELL0)) SP_MAIN LO C0 (mseg_addr M0 0) RC0 NM0.
Proof. unfold query_pre. sat. Qed.

(** reac_segconf_model, LLVMFuzzerTestOneInput 0x13b2c, and check_absent 0x14aac. *)
Lemma reac_segconf_model_pre_sat :
  query_pre MODEL_STACK (RMEM (RSQ R_CELL0)) SP_MAIN LO C0 (mseg_addr M0 0) RC0 NM0.
Proof. unfold query_pre. sat. Qed.

Lemma reac_segconf_model_pre_sat_absent :
  query_pre MODEL_STACK (RMEM RSP) (SP_MAIN - ABSENT_FRAME) LO C0 OUT RC0 PROBE0.
Proof. unfold query_pre. sat. Qed.

Lemma reac_segconf_model_pre_sat_nosuch :
  query_pre MODEL_STACK (RMEM RSP) (SP_MAIN - ABSENT_FRAME) LO C0 STR_NOSUCH RC0 S_nosuch.
Proof. unfold query_pre. sat. Qed.

(** reac_box_catalogue_by_token, reac_segconf_parse_file 0x152c8 (under reac_segconf_parse, the last file): token =
    low[24] at parse_file's sp + 0x140, holding the folded value of T0's model line. *)
Lemma reac_box_catalogue_by_token_pre_sat : by_token_pre (RMEM RST) SP_PF LO TOKA LOW0.
Proof. unfold by_token_pre. sat. Qed.

(** reac_box_catalogue_by_token under a drop-in file's reac_segconf_parse_file, which main calls itself
    (fuzz_segconf.c:613; an input whose first of two files is T0): the same token in low[24] of that frame. *)
Lemma reac_box_catalogue_by_token_pre_sat_dropin : by_token_pre (RMEM RST2) SP_PF2 LO TOKA2 LOW0.
Proof. unfold by_token_pre. sat. Qed.

(** check_segments, LLVMFuzzerTestOneInput 0x13aec: (c, m, returned). *)
Lemma check_segments_pre_sat :
  check_segments_pre (RMEM (RSQ R_CELL0)) SP_MAIN LO C0 M0 (b2z RET0) RC0 MC0 RET0.
Proof. unfold check_segments_pre. sat. Qed.

(** check_role, LLVMFuzzerTestOneInput 0x13b20: (set, r, g = &m->seg[0]). *)
Lemma check_role_pre_sat :
  check_role_pre (RMEM (RSQ R_CELL0)) SP_MAIN LO (match r_role RC0 NM0 with Some _ => 1 | None => 0 end) R_CELL0
    (mseg_addr M0 0) (r_role RC0 NM0) G0.
Proof. unfold check_role_pre. vmeq (r_role RC0 NM0). cbv beta iota. sat. Qed.

(** check_model, LLVMFuzzerTestOneInput 0x13b34: (reac_segconf_model's result, g). *)
Lemma check_model_pre_sat :
  check_model_pre (RMEM (RSQ R_CELL0)) SP_MAIN LO (model_ptr C0 RC0 NM0) (mseg_addr M0 0) (r_model RC0 NM0) G0.
Proof. unfold check_model_pre. vmeq (r_model RC0 NM0). cbv beta iota. sat. Qed.

(** check_ignore, LLVMFuzzerTestOneInput 0x13b48: (reac_segconf_ignored's result, g). *)
Lemma check_ignore_pre_sat :
  check_ignore_pre (RMEM (RSQ R_CELL0)) SP_MAIN LO (b2z (r_ignored RC0 NM0)) (mseg_addr M0 0) (r_ignored RC0 NM0) G0.
Proof. unfold check_ignore_pre. sat. Qed.

(** check_provenance, LLVMFuzzerTestOneInput 0x13b74: (role_file's result, ignore_file's result, g). *)
Lemma check_provenance_pre_sat :
  check_provenance_pre (RMEM (RSQ R_CELL0)) SP_MAIN LO (role_file_ptr C0 RC0 NM0) (ignore_file_ptr C0 RC0 NM0)
    (mseg_addr M0 0) (r_role_file RC0 NM0) (r_ignore_file RC0 NM0) G0.
Proof.
  unfold check_provenance_pre. vmeq (r_role_file RC0 NM0). vmeq (r_ignore_file RC0 NM0). cbv beta iota. sat.
Qed.

(** check_refusals, LLVMFuzzerTestOneInput 0x13b90: (c, m). *)
Lemma check_refusals_pre_sat : check_refusals_pre (RMEM (RSQ R_CELL0)) SP_MAIN LO C0 M0 RC0 MC0.
Proof. unfold check_refusals_pre. sat. Qed.

(** check_address, LLVMFuzzerTestOneInput 0x13bd8: (c->refusal[0], m->kept[0]). *)
Lemma check_address_pre_sat :
  check_address_pre (RMEM (RSQ R_CELL0)) SP_MAIN LO (refusal_addr C0 0) (kept_addr M0 0)
    (nth 0 (rc_refusal RC0) []) (fst (nth 0 (mc_kept MC0) ([], false))).
Proof. unfold check_address_pre. sat. Qed.

(** check_knock_refused, LLVMFuzzerTestOneInput 0x13be4: (c->refusal[0], m->kept_knock[0] = 1). *)
Lemma check_knock_refused_pre_sat :
  check_knock_refused_pre (RMEM (RSQ R_CELL0)) SP_MAIN LO (refusal_addr C0 0)
    (b2z (snd (nth 0 (mc_kept MC0) ([], false)))) (nth 0 (rc_refusal RC0) []) (snd (nth 0 (mc_kept MC0) ([], false))).
Proof.
  unfold check_knock_refused_pre. csplit;
    (lazymatch goal with |- exists g, bytes_at _ _ _ (le8 g) => exists (Z_to_bv 64 0) | |- _ => idtac end); sg.
Qed.

(** check_absent, LLVMFuzzerTestOneInput 0x13c50 (the probe) and 0x13c88 ("nosuch0"). *)
Lemma check_absent_pre_sat : check_absent_pre (RMEM RSP) SP_MAIN LO C0 OUT RC0 PROBE0.
Proof. unfold check_absent_pre, query_pre. sat. Qed.

Lemma check_absent_pre_sat_nosuch : check_absent_pre (RMEM RSP) SP_MAIN LO C0 STR_NOSUCH RC0 S_nosuch.
Proof. unfold check_absent_pre, query_pre. sat. Qed.

(** check_declared, LLVMFuzzerTestOneInput 0x13f3c: (got, want, tab, n, mt, mn, cap). *)
Lemma check_declared_pre_sat :
  check_declared_pre (RMEM RSD) SP_MAIN LO (fst GOT0 mod 2 ^ 64) (fst WANT0 mod 2 ^ 64) TAB0
    (Z.of_nat (length (snd GOT0))) MT0 (Z.of_nat (length (snd WANT0))) CAP0
    (fst GOT0) (fst WANT0) (snd GOT0) (snd WANT0).
Proof. unfold check_declared_pre. sat. Qed.
