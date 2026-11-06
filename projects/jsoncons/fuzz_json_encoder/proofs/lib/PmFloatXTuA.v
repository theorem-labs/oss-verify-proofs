(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmFloatXSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMFXTA.
Definition len (bs : list Z) : Z := Z.of_nat (length bs).   (* [comment removed for export] *)
Section SpecsA.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.
Variable CL : Z.
Abbreviation stransA := (PMESA.stransA L ar HI IC CL).
Abbreviation stransA_w := (PMESA.stransA_w L ar HI IC CL).

(* [comment removed for export] *)
Definition rd_bufA (M : PMSA.mem) (FF : list fframe) (buf n g S2 SK : Z) (bs : list Z) : Prop :=
  L5.bytes_at (hl_segs L) M buf bs /\ L5.defined M buf n /\ len bs = n /\ PMSA.ainfr FF buf (8 * g) /\ buf mod 8 = 0 /\ shadow_zero M buf g /\ n <= 8 * g /\
  PMLA.apart buf (8 * g) S2 24 /\ PMLA.apart buf (8 * g) SK 8.

(* [comment removed for export] *)
Definition dump_buffer_x_specA (pc : Z) : Prop :=
  forall (buf n dp : Z) (bs : list Z),
    stransA pc PMFXA.DB_SCR_A 0
      (fun _ FF sp R M SK => PMSA.a0 R buf /\ PMSA.a1 R n /\ PMSA.a2 R dp /\ 0 <= dp < 256 /\ PMSA.a3 R SK /\ 1 <= n <= 25 /\
                              exists S2, PMSA.u64 L M SK S2 /\ 0 <= S2 < 2 ^ 64 /\ rd_bufA M FF buf n 4 S2 SK bs)
      (fun _ _ => True)
      (fun pay => 1 <= pay <= n + 2) 27.

(* [comment removed for export] *)
Definition prettify_x_specA (pc : Z) : Prop :=
  forall (buf n k : Z) (bs : list Z),
    stransA pc PMFXA.PR_SCR_A 0
      (fun _ FF sp R M SK => PMSA.a0 R buf /\ PMSA.a1 R n /\ PMSA.a2 R k /\ PMSA.a3 R (2 ^ 64 - 4) /\ getr R 14%bv = Z_to_bv 64 17 /\ getr R 15%bv = Z_to_bv 64 SK /\
                              1 <= n <= 21 /\ -343 <= k <= 309 /\ exists S2, PMSA.u64 L M SK S2 /\ 0 <= S2 < 2 ^ 64 /\ rd_bufA M FF buf n 4 S2 SK bs)
      (fun _ _ => True)
      (fun pay => 2 <= pay <= 27) 27.

(* [comment removed for export] *)
Definition dtoa_false_x_specA (pc : Z) : Prop :=
  forall (dp : Z),
    stransA_w pc PMFXA.DF_SCR_A 3 [(hl_tp L - 164, 4)]
      (fun _ _ sp R M SK => PMSA.a0 R dp /\ 0 <= dp < 256 /\ PMSA.a1 R SK /\ sp mod 32 = 0)
      (fun R' _ => PMSA.a0 R' 1)
      (fun pay => 1 <= pay <= 27) 27.

(* [comment removed for export] *)
Definition dtoa_true_x_specA (pc : Z) : Prop :=
  forall (dp : Z),
    stransA_w pc PMFXA.DT_SCR_A 4 [(hl_tp L - 164, 4)]
      (fun _ _ sp R M SK => PMSA.a0 R dp /\ 0 <= dp < 256 /\ PMSA.a1 R SK /\ PMSA.a2 R 0 /\ sp mod 32 = 0)
      (fun R' _ => PMSA.a0 R' 1)
      (fun pay => 1 <= pay <= 28) 28.


(* [comment removed for export] *)
Definition vtranseA (WD_SCRA : Z) (pc : Z) (ev : PMES.eev) (Args : list (Z * Z) -> list fframe -> Z -> Z -> Z -> bvmap 5 word -> PMSA.mem -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 kx bx : Z) (g : PMES.eghost),
    PMSA.cps_asan L ar HI pc r sp (PMESA.VIS_SCRA WD_SCRA) (LBo ++ PMES.g_lbv g) FF LK cr A PMESA.VIS_D
      (fun R M => PMSA.a0 R V /\ Args LBo FF sp V S2 R M /\ sp mod 32 = 0 /\ PMSA.stksh ar M sp (PMESA.VIS_SCRA WD_SCRA) /\ PMESA.enc_invA L IC EC M V S2 g /\
                  PMES.ev_guard (PMES.g_es g) ev /\ PMESA.eroomA CL g ev /\
                  PMLA.img_ro IC M /\ PMESA.lits_ok L IC M /\ PMESA.ecreditA L CL cr g kx bx /\ PMSA.fobj M FF V PMES.ENC_SIZE /\ PMSA.fobj M FF S2 24 /\ PMLA.apart V PMES.ENC_SIZE S2 24)
      (fun R M R' M' LB' cr' LBk W => exists (g' : PMES.eghost) (pay : Z),
          PMSA.a0 R' 1 /\ PMESA.enc_invA L IC EC M' V S2 g' /\ PMES.g_es g' = PMES.estep (PMES.g_es g) ev /\ PMES.pay_ok ev pay /\
          PMES.g_len g' = PMES.g_len g + PMES.ev_ind (PMES.g_es g) ev + pay /\
          PMESA.lits_ok L IC M' /\ LB' = LBo ++ PMES.g_lbv g' /\ LBk = LBo /\ W = PMESA.W_encA IC V S2 ++ [(hl_tp L - 164, 4)] /\ PMESA.ecreditA L CL cr' g' kx bx).
Definition visit_double_xe_specA (WD_SCRA pc : Z) : Prop := vtranseA WD_SCRA pc PMES.EvDbl PMESA.argT.
(* [comment removed for export] *)
End SpecsA.
Lemma DT_SCR_A_val : 96 + PMFXA.DT_SCR_A = 12640. Proof. vm_compute. reflexivity. Qed.
End PMFXTA.
