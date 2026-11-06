(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:106-109
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* k_def of seg_K (LLVMFuzzerTestOneInput_seg_K_hand_stmt.v, k_def_stmt), fuzz_identity.asan-ubsan
   +0x1ae8 .. +0x1bec (0x8225c .. 0x82360): count = 11 (0x82260, not taken); the row
   e = BOX_CATALOGUE + 296 * (t_row mod 11) (0x8226c..0x82278) and its two UBSan tests (0x8227c, 0x8228c, refuted);
   reac_box_catalogue_defect (e, t_in, t_out, dp) at 0x822a8 (k_defect_at); the inline mask 0x822b0..0x82350 (the
   alignment trap 0x822b8, the ASan checks of e+16, e+20 (4 bytes) and e+8 (8 bytes), the I / O compares, P, the
   strcmp wrapper on (P, dp) at 0x82344 when P <> 0, k_strcmp_at); the mask compare 0x82354 (equal: both are
   CATALOGUE_DEFECT_MASK); count's shadow byte poisoned again (0x8235c). kd_pre is the run to the call. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81 IdentBlkTail.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
check_str reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_K_hand_stmt LLVMFuzzerTestOneInput_seg_K_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* +0x1ae8: atoms 32 = t_row, 33 = t_in, 34 = t_out, 35 = dp. Region 0: the machine frame's slots the
   stretch loads (base x9 = mf; read-only); region 1: `count` (base x18 = SF + 720; read-only, 11). *)
Definition kd_rmf : YP09.region := YP09.mkRegion (Some 9%nat) 112 192 112 112
  [YP09.mkChunk 112 (CVal 8 (SOff 32 0)); YP09.mkChunk 160 (CVal 8 (SOff 34 0));
   YP09.mkChunk 176 (CVal 8 (SOff 33 0)); YP09.mkChunk 184 (CVal 8 (SOff 35 0))].
Definition kd_rcnt : YP09.region := YP09.mkRegion (Some 18%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 11))].
Definition kd_ss1 : sstate := mkSS 0x1ae8 sr_atoms [kd_rmf; kd_rcnt] None (mkFacts [] [] []).
Ltac kd_awr_ro1 :=
  intros ?a (rr & Hrr & Ha); unfold kd_ss1 in Hrr; cbn [ss_mem In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [unfold kd_rmf, kd_rcnt in Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia | ]);
  destruct Hrr.
Section kdl. Context {fx : YK11.FPState}.
(* The row address the stretch 0x8226c..0x82278 computes: s4 = s6 + 296 * (t_row remu 11). *)
Lemma kd_rowU : forall E cat trow, ew E 10 = Z_to_bv 64 cat -> 0 <= cat -> cat + 2960 < 2 ^ 64 ->
  ew E 32 = Z_to_bv 64 trow -> 0 <= trow < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SMd M_REMU (SOff 32 0) (SLit 11)) (SLit 296))) =
  cat + 296 * (trow mod 11).
Proof.
intros E cat trow H10 Hc0 Hc1 H32 Ht.
rewrite U_SAlu, U_SMd, U_SMd, (U_atom E 10 cat H10 ltac:(lia)), (U_atom E 32 trow H32 Ht), !U_lit by lia.
cbn [zalu_raw zmd_raw]. try change (11 =? 0) with false. try change (296 =? 0) with false. cbv iota.
pose proof (Z.mod_pos_bound trow 11 ltac:(lia)) as R.
unfold zcanon, M64. rewrite (Z.mod_small (trow mod 11) (2 ^ 64)) by lia.
rewrite (Z.mod_small (trow mod 11 * 296) (2 ^ 64)) by lia.
rewrite (Z.mod_small (cat + trow mod 11 * 296) (2 ^ 64)) by lia. lia.
Qed.
(* The UBSan test 0x82280..0x8228c: (s6 <> 0) xor (s4 = 0) is 1 for a non-null table. *)
Lemma kd_trapU : forall E cat trow, ew E 10 = Z_to_bv 64 cat -> 1 <= cat -> cat + 2960 < 2 ^ 64 ->
  ew E 32 = Z_to_bv 64 trow -> 0 <= trow < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 10 0))
    (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SMd M_REMU (SOff 32 0) (SLit 11)) (SLit 296))) (SLit 1)))
  = 1.
Proof.
intros E cat trow H10 Hc0 Hc1 H32 Ht.
rewrite U_SAlu, U_SAlu, U_SAlu, (kd_rowU E cat trow H10 ltac:(lia) Hc1 H32 Ht),
  (U_atom E 10 cat H10 ltac:(lia)), !U_lit by lia.
pose proof (Z.mod_pos_bound trow 11 ltac:(lia)) as R.
cbn [zalu_raw].
replace (0 <? cat) with true by (symmetry; apply Z.ltb_lt; lia).
replace (cat + 296 * (trow mod 11) <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
reflexivity.
Qed.
End kdl.
Ltac kd_noin :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Ha := fresh "Ha" in
  intros (rr & Hrr & Ha); vm_compute in Hrr;
  repeat (destruct Hrr as [<- | Hrr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; exfalso; clear - Ha; lia | ]);
  destruct Hrr.
Ltac kd_awr_ro := intros ?a; kd_noin.
Ltac kd_ro_eq HM :=
  lazymatch goal with HFr' : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- _ =>
    assert (HM : forall x, mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x)
      by (let x := fresh "x" in intros x; apply HFr'; kd_noin)
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* a register of a state, without unfolding its symbolic value *)
Ltac kreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Section kdl2. Context {fx : YK11.FPState}.
(* s3 after 0x82348..0x82350: s3 | 2 * (a0 <> 0). *)
Lemma kd_fin : forall E s0 v, ew E 19 = Z_to_bv 64 s0 -> (s0 = 0 \/ s0 = 1) -> ew E 10 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  U E (SAlu ALU_OR (SOff 19 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 10 0)) (SLit 1))) =
  s0 + (if v =? 0 then 0 else 2).
Proof.
intros E s0 v H19 Hs H10 Hv.
rewrite !U_SAlu, (U_atom E 19 s0 H19 ltac:(lia)), (U_atom E 10 v H10 Hv), !U_lit by lia.
cbn [zalu_raw].
destruct (Z.eqb_spec v 0) as [->|NZ].
- destruct Hs as [-> | ->]; vm_compute; reflexivity.
- replace (0 <? v) with true by (symmetry; apply Z.ltb_lt; lia). destruct Hs as [-> | ->]; vm_compute; reflexivity.
Qed.
End kdl2.
(* +0x1b38 (0x822ac, the return of reac_box_catalogue_defect): atoms 32 = the shadow base (mf+168), 33 = P,
   34 = I mod 2^32, 35 = O mod 2^32, 36 = dp. Region 0: mf+168 and mf+184 (read-only); region 1: the row's
   P / I / O (base x20 = e; read-only); region 2: count's shadow byte (base x23 = shadow(SF), offset 90;
   written at 0x8235c). Shadow entry: e+8 .. e+24 (the ASan tests of e+16, e+20 and e+8). *)
Definition kd_SB : Z := 0x7fff8000.
Definition kd_Bx : sv := SOff 32 0.
Definition kd_Bspan : Z * Z := (kd_SB, kd_SB + 2 ^ 44 - 1).
Definition kd_rmf2 : YP09.region := YP09.mkRegion (Some 9%nat) 168 192 168 168
  [YP09.mkChunk 168 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 36 0))].
Definition kd_rrow : YP09.region := YP09.mkRegion (Some 20%nat) 8 24 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 4 (SOff 34 0)); YP09.mkChunk 20 (CVal 4 (SOff 35 0))].
Definition kd_rsh : YP09.region := YP09.mkRegion (Some 23%nat) 90 91 90 91 [].
Definition kd_facts2 : facts :=
  mkFacts [(32%nat, mkAF kd_SB kd_SB 0); (20%nat, mkAF 0x8000 IMG_TOP 3); (22%nat, mkAF 0x8000 IMG_TOP 3);
    (34%nat, mkAF 0 4294967295 0); (35%nat, mkAF 0 4294967295 0)] [] [].
Definition kd_ss2 : sstate := mkSS 0x1b38 sr_atoms [kd_rmf2; kd_rrow] None kd_facts2.
Definition kd_SH : list shent := [mkSHE 20 8 24].
(* +0x1be0 (0x82354): only count's shadow byte (base x23 = shadow(SF), offset 90), written at 0x8235c. *)
Definition kd_ss3 : sstate := mkSS 0x1be0 sr_atoms [YP09.mkRegion (Some 23%nat) 90 91 90 91 []] None (mkFacts [] [] []).
(* +0x1bd4 (0x82348, the return of the strcmp wrapper): no memory. *)
Definition kd_ss4 : sstate := mkSS 0x1bd4 sr_atoms [] None (mkFacts [] [] []).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
#[local] Notation KPREn := (KPRE B RLO RHI LLVMF_STK arodata_okS G).
#[local] Notation KHn := (KH B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation KCn := (KC B LLVMF_STK).

(* k_defect_at of LLVMFuzzerTestOneInput_seg_K_base.v with the frame clause the owners' fix adds LAST to its post
   (memory outside the callee's own stack window unchanged). Local premise of k_def_A until the callee and base
   land; then it is k_defect_at itself. *)
Definition kd_defect_at_A : Prop :=
  forall W regsc memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch1
  (e i o' d I O P : Z) (sP sd : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  getr regsc 10 = w64 e -> getr regsc 11 = w64 i -> getr regsc 12 = w64 o' -> getr regsc 13 = w64 d ->
  0 <= e < 2 ^ 64 -> -2 ^ 31 <= i < 2 ^ 31 -> -2 ^ 31 <= o' < 2 ^ 31 -> 0 <= d < 2 ^ 64 ->
  -2 ^ 31 <= I < 2 ^ 31 -> -2 ^ 31 <= O < 2 ^ 31 -> 0 <= P < 2 ^ 64 ->
  (e <> 0 ->
   IMG_LO <= e + 8 /\ e + 24 <= IMG_TOP /\ reac_box_catalogue_defect.catd_glob G (e + 8) 16 /\
   e mod 8 = 0 /\
   (e + 24 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= e + 8) /\
   (e + 24 <= VAL (A_OBJ 31) \/ VAL (A_OBJ 31) + 8 <= e + 8) /\
   val_mem SEGS (mrestrict (w_H W) memc) (e + 8) 8 P /\
   val_mem SEGS (mrestrict (w_H W) memc) (e + 16) 4 I /\
   val_mem SEGS (mrestrict (w_H W) memc) (e + 20) 4 O) ->
  (e <> 0 -> d <> 0 -> P <> 0 ->
   reac_box_catalogue_defect.catd_rostr G W memc P sP /\ reac_box_catalogue_defect.catd_hpstr B lyc Sc W memc d sd) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_reac_box_catalogue_defect)) memc (seg_rom SEGS)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 0) /\
    ajournal SEGS B reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK (sp0 + o) [] lyc Sc W memc mdc []
      ly2 S2 W2 mem2 md2 0 /\
    aregs_preserved regsc regs2 /\
    (getr regs2 10 = w64 (reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK e i o' d I O P sP sd) /\
     ly2 = lyc /\ S2 = Sc /\ W2 = W /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK <= a < sp0 + o) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a))).
Section h.
Hypothesis HPRE : KPREn.
Let LAWS := k_laws B RLO RHI LLVMF_STK arodata_okS G HPRE.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Section run.
Variables (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model).
Hypothesis HKH : KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2.
Let GEOM := k_geom B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH.
Let VMHI := k_vm_hi B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH.

Ltac kd_awr2 U23 G12 :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Ha := fresh "Ha" in let a := fresh "a" in
  intros a (rr & Hrr & Ha); vm_compute in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ exfalso; clear - Ha; lia
            | rewrite ?ew_havoc_old in Ha by lia; rewrite U23 in Ha;
              right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
              unfold in_zr; cbn [fst snd]; rewrite G12; change (fs_frame_bytes 4 / 8) with 128; clear - Ha; lia ]
    | ]);
  destruct Hrr.

Ltac kd_upd :=
  lazymatch goal with
  | HFr' : frame_of _ _ (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    HM : forall x : word, mrestrict (w_H ?W) ?m1 x = mrestrict (w_H ?W) ?m0 x |- _ =>
    let HM' := fresh "HM" in
    assert (HM' : forall x : word, mrestrict (w_H W) m2 x = mrestrict (w_H W) m0 x)
      by (let x := fresh "x" in intros x; transitivity (mrestrict (w_H W) m1 x); [apply HFr'; kd_noin | exact (HM x)]);
    clear HM; rename HM' into HM
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Ltac kd_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  lia.

Lemma kd_kkeep_eq : forall m m', kkeep B g pos mf ly2 S2 W2 mem2 m ->
  (forall x, mrestrict (w_H W2) m' x = mrestrict (w_H W2) m x) -> kkeep B g pos mf ly2 S2 W2 mem2 m'.
Proof.
intros m m' (K1 & K2 & K3) HM.
assert (AV : forall a, aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a) by (intros a; apply aview_eq_of; apply HM).
split; [intros a H1 H2; rewrite AV; exact (K1 a H1 H2)|].
split; [intros b n i H1 H2; rewrite AV; exact (K2 b n i H1 H2)|].
intros a H1 H2 H3; rewrite AV; exact (K3 a H1 H2 H3).
Qed.

(* +0x1ae8 .. the call at +0x1b34 (0x8225c .. 0x822a8): count = 11 is not 0 (0x82260), the row
   s4 = s6 + 296 * (t_row remu 11) (0x8226c..0x82278), its two UBSan tests (0x8227c, 0x8228c, refuted:
   no overflow, table non-null), a0..a3 = row, t_in (mf+176), t_out (mf+160), dp (mf+184). The run
   writes nothing. *)
Lemma kd_pre : forall regs mem md (Q : world SEGS -> config -> Prop),
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md -> getr regs 18 = w64 (SFa g pos + V_cnt) ->
  getr regs 10 = w64 (VAL reac_box_catalogue.CAT_OBJ) ->
  val_mem SEGS (rd W2 mem) (SFa g pos + V_cnt) 8 reac_box_catalogue.BOX_COUNT ->
  (forall (regsc : bvmap 5 word) memc mdc,
    ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
      ly2 S2 W2 memc mdc (4 * Z.of_nat (m_nrec g) + 7) ->
    kkeep B g pos mf ly2 S2 W2 mem2 memc ->
    getr regsc 2 = w64 mf -> getr regsc 9 = w64 mf -> getr regsc 8 = w64 (e_sp0 g) ->
    getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
    getr regsc 21 = w64 tk -> getr regsc 23 = w64 (shadow_addr (SFa g pos)) ->
    getr regsc 1 = Z_to_bv 64 (BASE + 0x1b38) ->
    getr regsc 10 = w64 (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11)) ->
    getr regsc 11 = w64 (SlotModel.t_in (e_pl g)) -> getr regsc 12 = w64 (SlotModel.t_out (e_pl g)) ->
    getr regsc 13 = w64 dp ->
    getr regsc 20 = w64 (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11)) ->
    getr regsc 22 = w64 (VAL reac_box_catalogue.CAT_OBJ) ->
    getr regsc 19 = w64 (SlotModel.t_in (e_pl g)) -> getr regsc 24 = w64 (SlotModel.t_out (e_pl g)) ->
    SRr SEGS W2 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_reac_box_catalogue_defect)) memc (seg_rom SEGS)) mdc) Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ae8) regs mem md) Q.
Proof.
intros regs mem md Q (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh) R18 R10 VC HCALL.
pose proof GEOM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof HKH as (HJ2 & HFR & HK & HMLE & HMOK & HEC & HHB & HSR & _ & _ & _ & _ & _ & V152 & V184 & V144 & V128
  & V120 & V176 & V160 & V112 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 8)) as Rrow.
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 1)) as Rin.
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 2)) as Rout.
change (SlotModel.inb (e_pl g) (SlotModel.cT (e_pl g) + 8)) with (SlotModel.t_row (e_pl g)) in Rrow.
change (SlotModel.inb (e_pl g) (SlotModel.cT (e_pl g) + 1)) with (SlotModel.t_in (e_pl g)) in Rin.
change (SlotModel.inb (e_pl g) (SlotModel.cT (e_pl g) + 2)) with (SlotModel.t_out (e_pl g)) in Rout.
set (trow := SlotModel.t_row (e_pl g)) in *. set (tin := SlotModel.t_in (e_pl g)) in *.
set (tout := SlotModel.t_out (e_pl g)) in *. set (SF := SFa g pos) in *.
destruct HHB as [Hperm _].
assert (Hindp : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly2 S2)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. right. right. left. reflexivity. }
pose proof (proj1 HJ2) as HAR2.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 dp _ HAR2 Hindp) as (_ & Hdp4096 & Hdpceil & _).
pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(lia)) as Hrq.
assert (Hdp : 4096 <= dp < alloc_ceiling) by (clear - Hdp4096 Hdpceil Hrq; lia).
clear Hperm Hindp Hdp4096 Hdpceil Hrq.
(* the image at mem: BOX_CATALOGUE's rows *)
pose proof (k_aro B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH mem md HJ) as (HAP & _).
pose proof (k_himg _ _ _ _ _ _ HPRE W2 mem HAP) as HIMG0.
pose proof HIMG0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROW).
pose proof (HROW 10 ltac:(unfold reac_box_catalogue.BOX_COUNT; lia)) as (_ & H28top & _).
pose proof (HROW 0 ltac:(unfold reac_box_catalogue.BOX_COUNT; lia)) as (H28lo & _).
clear HROW HIMG0 HAP.
pose proof (pa_val_range (A_OBJ 28)) as R28.
change (VAL (A_OBJ 28)) with (VAL reac_box_catalogue.CAT_OBJ) in H28top, H28lo, R28.
set (CAT := VAL reac_box_catalogue.CAT_OBJ) in *.
(* the machine frame's slots at mem *)
assert (M112 : val_mem SEGS (rd W2 mem) (mf + 112) 8 trow) by (apply (VMHI mem _ 8 _ HKP); [clear; lia | clear - G1 G2 G3; lia | exact V112]).
assert (M160 : val_mem SEGS (rd W2 mem) (mf + 160) 8 tout) by (apply (VMHI mem _ 8 _ HKP); [clear; lia | clear - G1 G2 G3; lia | exact V160]).
assert (M176 : val_mem SEGS (rd W2 mem) (mf + 176) 8 tin) by (apply (VMHI mem _ 8 _ HKP); [clear; lia | clear - G1 G2 G3; lia | exact V176]).
assert (M184 : val_mem SEGS (rd W2 mem) (mf + 184) 8 dp) by (apply (VMHI mem _ 8 _ HKP); [clear; lia | clear - G1 G2 G3; lia | exact V184]).
(* the environment *)
remember (Eimg (Ereg regs [Z_to_bv 64 trow; Z_to_bv 64 tin; Z_to_bv 64 tout; Z_to_bv 64 dp])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 trow)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 tin)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 tout)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 dp)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (E10 : ew E 10 = Z_to_bv 64 CAT) by (rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - G1 G2 G3 C1. lia. }
assert (U18 : bv_unsigned (ew E 18) = SF + 720).
{ rewrite (EE 18%nat 18%bv eq_refl), R18. unfold V_cnt. apply unsigned_lit_small. clear - G8 G9 C1. lia. }
assert (HS : st_ok_pi SEGS VAL E kd_ss1
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x1ae8)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kd_ss1. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold kd_rmf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - G1 C1; lia|]. split; [clear - G1 G2 G3; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * apply (chunk_ok_val SEGS E _ mf 112 8 (SOff 32 0) trow);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rrow; lia | clear; lia | exact M112].
      * apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 34 0) tout);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rout; lia | clear; lia | exact M160].
      * apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 33 0) tin);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rin; lia | clear; lia | exact M176].
      * apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 35 0) dp);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hdp C1; lia | clear; lia | exact M184].
    + unfold kd_rcnt, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U18. split; [clear - G8; lia|]. split; [clear - G9 C1; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SF + 720) 0 8 (SLit 11) 11); [reflexivity | clear; lia | clear; lia |].
      rewrite Z.add_0_r. exact VC.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, kd_rmf, kd_rcnt.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18.
    split; [split; [|exact I] | split; exact I].
    right. clear - G1 G9. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x1ae8)) with (Z_to_bv 64 (BASE + 0x1ae8)).
(* run 1: to the overflow test 0x8227c *)
paj_run_shc RUNP RUNC HS HJ.
{ kd_awr_ro. }
kd_ro_eq HM1.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U, (kd_rowU E CAT trow E10 ltac:(clear - R28; lia) ltac:(clear - H28top; lia) E32
    ltac:(clear - Rrow; lia)), (U_atom E 10 CAT E10 ltac:(clear - R28; lia)) in Hc.
  apply Z.ltb_lt in Hc. pose proof (Z.mod_pos_bound trow 11 ltac:(lia)). clear - Hc H. lia. }
clear Hc.
(* run 2: to the null-table test 0x8228c *)
paj_run_shc RUNP RUNC HS HJ.
{ kd_awr_ro. }
kd_ro_eq HM2.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_eq_U, (kd_trapU E CAT trow E10 ltac:(clear - H28lo; lia) ltac:(clear - H28top; lia) E32
    ltac:(clear - Rrow; lia)), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
(* run 3: to the call at 0x822a8 *)
paj_run_shc RUNP RUNC HS HJ.
{ kd_awr_ro. }
kd_ro_eq HM3.
kreg HS (10%bv : bv 5) K10. kreg HS (20%bv : bv 5) K20.
prreg HS (11%bv : bv 5) K11. prreg HS (12%bv : bv 5) K12. prreg HS (13%bv : bv 5) K13.
prreg HS (1%bv : bv 5) K1r. prreg HS (2%bv : bv 5) K2. prreg HS (9%bv : bv 5) K9. prreg HS (8%bv : bv 5) K8.
prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (21%bv : bv 5) K21. prreg HS (23%bv : bv 5) K23.
prreg HS (22%bv : bv 5) K22. prreg HS (19%bv : bv 5) K19. prreg HS (24%bv : bv 5) K24.
pose proof (Z.mod_pos_bound trow 11 ltac:(lia)) as Rr11.
assert (UE : U E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SMd M_REMU (SOff 32 0) (SLit 11)) (SLit 296))) =
  CAT + 296 * (trow mod 11))
  by exact (kd_rowU E CAT trow E10 ltac:(clear - R28; lia) ltac:(clear - H28top; lia) E32 ltac:(clear - Rrow; lia)).
rewrite denot_lit_U, U_SAlu, UE, U_lit in K10 by lia. cbn [zalu_raw] in K10. rewrite Z.add_0_r in K10.
unfold zcanon, M64 in K10. rewrite Z.mod_small in K10 by (clear - R28 H28top Rr11; lia).
rewrite denot_lit_U, UE in K20.
pose proof (k_psig _ _ _ _ _ _ HPRE) as PSIG.
pmkst HS.
rewrite (PSIG IB_reac_box_catalogue_defect AF_reac_box_catalogue_defect eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ (ms_mem ?msc) _) _) _ =>
  assert (HMc : forall x, mrestrict (w_H W2) (ms_mem msc) x = mrestrict (w_H W2) mem x)
    by (intros x; rewrite HM3, HM2, HM1; reflexivity) end.
apply HCALL.
- exact HJ.
- exact (kd_kkeep_eq mem _ HKP HMc).
- rewrite K2, (EE 2%nat 2%bv eq_refl). exact Rsp.
- rewrite K9, (EE 9%nat 9%bv eq_refl). exact Rs1.
- rewrite K8, (EE 8%nat 8%bv eq_refl). exact Rs0.
- rewrite K3, (EE 3%nat 3%bv eq_refl). exact Rgp.
- rewrite K4, (EE 4%nat 4%bv eq_refl). exact Rtp.
- rewrite K21, (EE 21%nat 21%bv eq_refl). exact Rtk.
- rewrite K23, (EE 23%nat 23%bv eq_refl). exact Rsh.
- exact K1r.
- exact K10.
- rewrite K11. exact E33.
- rewrite K12. exact E34.
- rewrite K13. exact E35.
- exact K20.
- rewrite K22. exact E10.
- rewrite K19. exact E33.
- rewrite K24. exact E34.
Qed.

(* The tail +0x1be0 .. +0x1bec (0x82354 .. 0x82360): the mask compare (equal, so 0x82614 is not reached), then
   count's shadow byte (shadow(SF) + 90) poisoned with 0xf8. *)
Lemma kd_tail : forall (regs : bvmap 5 word) m md (Q : world SEGS -> config -> Prop),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 m md (4 * Z.of_nat (m_nrec g) + 7) ->
  kkeep B g pos mf ly2 S2 W2 mem2 m ->
  getr regs 2 = w64 mf -> getr regs 9 = w64 mf -> getr regs 8 = w64 (e_sp0 g) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 21 = w64 tk -> getr regs 23 = w64 (shadow_addr (SFa g pos)) ->
  getr regs 18 = getr regs 19 ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1bec) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1be0) regs m md) Q.
Proof.
intros regs m md Q HJ HKP Rsp Rs1 Rs0 Rgp Rtp Rtk Rsh R1819 HQ.
pose proof GEOM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (SF := SFa g pos) in *. set (sh := shadow_addr SF) in *.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U23 : bv_unsigned (ew E 23) = sh).
{ rewrite (EE 23%nat 23%bv eq_refl), Rsh. apply unsigned_lit_small. clear - G14 G15 C1. lia. }
assert (HS : st_ok_pi SEGS VAL E kd_ss3
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x1be0)) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kd_ss3. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [clear - G14; lia|]. split; [clear - G15 C1; lia|].
    split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS).
    apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] ly2 S2 W2 m md _ (sh + o) HJ ltac:(
      right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; rewrite G12; change (fs_frame_bytes 4 / 8) with 128; fold SF; fold sh; clear - Ho; lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; exact Logic.I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact Logic.I | split; exact Logic.I]. }
unfold cfg_at. change (w64 (BASE + 0x1be0)) with (Z_to_bv 64 (BASE + 0x1be0)).
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
  rewrite (EE 18%nat 18%bv eq_refl), (EE 19%nat 19%bv eq_refl), R1819, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
paj_run_to_sh RUNTOP HS HJ 0x1bec.
{ kd_awr2 U23 G12. }
cbn [ms_mem mkst] in HF, HFr, HG, HJ.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
assert (KF : forall a, 0 <= a < 2 ^ 64 -> a <> sh + 90 ->
  aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) m a) end.
{ intros a Ha Hne.
  apply (kept_of_frame E _ (w_H W2) m _ (fun x => x = sh + 90) HFr); [|exact Ha|exact Hne].
  intros bb wlo whi aa Hin Hr. vm_compute in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr. rewrite U23 in Hr. clear - Hr. lia. }
clear HF HFr HG.
prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23.
pmkst HS.
apply HQ.
destruct HKP as (K1 & K2 & K3).
assert (Hsh90 : sh + 90 < alloc_ceiling) by (clear - G15; lia).
split; [exact HJ|].
split.
{ split; [|split].
  - intros a Ha Hw. rewrite KF by (clear - Ha Hsh90 C1; lia). exact (K1 a Ha Hw).
  - intros b n i Hb Hi. pose proof (proj1 HJ) as HARm.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 _ _ b n HARm Hb) as (_ & Hb4096 & Hbceil & Happ & _).
    rewrite KF; [exact (K2 b n i Hb Hi) | clear - Hb4096 Hbceil Hi C1; lia |].
    intros Heq. apply (fshadow_not_app SF 128 b (req_size n) (b + i)); [exact G8 | clear - G9 C1; lia | exact Happ | | clear - Hi; lia].
    rewrite Heq. unfold sh in *. rewrite G13. unfold SHADOW_OFF. clear. lia.
  - intros a Ha Hc Hs. rewrite KF; [exact (K3 a Ha Hc Hs) | | exact Hs].
    destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha; rewrite G12 in Ha;
    change (fs_frame_bytes 4) with 1024 in Ha; change (1024 / 8) with 128 in Ha; fold SF in Ha; fold sh in Ha;
    clear - Ha G8 G9 G14 G15 C1; lia. }
split; [rewrite P2; exact (EE 2%nat 2%bv eq_refl) || (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp)|].
split; [rewrite P9, (EE 9%nat 9%bv eq_refl); exact Rs1|].
split; [rewrite P8, (EE 8%nat 8%bv eq_refl); exact Rs0|].
split; [rewrite P3, (EE 3%nat 3%bv eq_refl); exact Rgp|].
split; [rewrite P4, (EE 4%nat 4%bv eq_refl); exact Rtp|].
split; [rewrite P21, (EE 21%nat 21%bv eq_refl); exact Rtk|].
rewrite P23, (EE 23%nat 23%bv eq_refl). exact Rsh.
Qed.

(* +0x1bd4 .. +0x1be0 (0x82348 .. 0x82354): s3 |= 2 * (strcmp <> 0), then the tail. *)
Lemma kd_after : forall (regs : bvmap 5 word) m md (Q : world SEGS -> config -> Prop) (s0 v M : Z),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 m md (4 * Z.of_nat (m_nrec g) + 7) ->
  kkeep B g pos mf ly2 S2 W2 mem2 m ->
  getr regs 2 = w64 mf -> getr regs 9 = w64 mf -> getr regs 8 = w64 (e_sp0 g) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 21 = w64 tk -> getr regs 23 = w64 (shadow_addr (SFa g pos)) ->
  getr regs 10 = w64 v -> 0 <= v < 2 ^ 64 -> getr regs 19 = w64 s0 -> (s0 = 0 \/ s0 = 1) ->
  getr regs 18 = w64 M -> M = s0 + (if v =? 0 then 0 else 2) ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1bec) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1bd4) regs m md) Q.
Proof.
intros regs m md Q s0 v M HJ HKP Rsp Rs1 Rs0 Rgp Rtp Rtk Rsh R10 Rv R19 Hs0 R18 HMv HQ.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (HS : st_ok_pi SEGS VAL E kd_ss4
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x1bd4)) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kd_ss4. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact Logic.I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact Logic.I | split; exact Logic.I]. }
unfold cfg_at. change (w64 (BASE + 0x1bd4)) with (Z_to_bv 64 (BASE + 0x1bd4)).
paj_run_sh RUNP HS HJ.
{ kd_awr_ro. }
cbn [ms_mem mkst] in HF, HFr, HG, HJ.
kd_ro_eq HM1.
kreg HS (19%bv : bv 5) K19.
prreg HS (18%bv : bv 5) P18. prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (21%bv : bv 5) P21. prreg HS (23%bv : bv 5) P23.
pmkst HS.
apply kd_tail.
- exact HJ.
- exact (kd_kkeep_eq m _ HKP HM1).
- rewrite P2, (EE 2%nat 2%bv eq_refl). exact Rsp.
- rewrite P9, (EE 9%nat 9%bv eq_refl). exact Rs1.
- rewrite P8, (EE 8%nat 8%bv eq_refl). exact Rs0.
- rewrite P3, (EE 3%nat 3%bv eq_refl). exact Rgp.
- rewrite P4, (EE 4%nat 4%bv eq_refl). exact Rtp.
- rewrite P21, (EE 21%nat 21%bv eq_refl). exact Rtk.
- rewrite P23, (EE 23%nat 23%bv eq_refl). exact Rsh.
- rewrite P18, K19, (EE 18%nat 18%bv eq_refl), R18, denot_lit_U.
  rewrite (kd_fin E s0 v ltac:(rewrite (EE 19%nat 19%bv eq_refl); exact R19) Hs0
    ltac:(rewrite (EE 10%nat 10%bv eq_refl); exact R10) Rv).
  rewrite HMv. reflexivity.
- exact HQ.
Qed.

Lemma kd_pres : forall (r : bv 5) (regs regs' : bvmap 5 word),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros r regs regs' H Hr. specialize (H (bv_unsigned r) Hr). rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* What a call below mf keeps, as kkeep: everything outside the callee's window [mf - 8208, mf). *)
Lemma kd_kkeep_win : forall m m' md0, AR SEGS B ly2 S2 W2 m md0 -> kkeep B g pos mf ly2 S2 W2 mem2 m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8208 <= a < mf) -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a) ->
  kkeep B g pos mf ly2 S2 W2 mem2 m'.
Proof.
intros m m' md0 HAR (K1 & K2 & K3) HW.
pose proof GEOM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof asan_consts as (C1 & _).
split; [|split].
- intros a Ha Hw. rewrite HW; [exact (K1 a Ha Hw) | clear - Ha C1; lia |]. unfold ESTACK in Hw. clear - Hw. lia.
- intros b n i Hb Hi. destruct (al_blocks _ _ LAWS ly2 S2 W2 m md0 b n HAR Hb) as (_ & Hb4096 & Hbceil & _).
  rewrite HW; [exact (K2 b n i Hb Hi) | clear - Hb4096 Hbceil Hi C1; lia | clear - Hb4096 Hbceil Hi G1; lia].
- intros a Ha Hc Hs. rewrite HW; [exact (K3 a Ha Hc Hs) | |].
  + destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha; rewrite G12 in Ha;
    change (fs_frame_bytes 4) with 1024 in Ha; change (1024 / 8) with 128 in Ha; clear - Ha G8 G9 G14 G15 C1; lia.
  + destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha; rewrite G12 in Ha;
    change (fs_frame_bytes 4) with 1024 in Ha; change (1024 / 8) with 128 in Ha; clear - Ha G1 G9 G15 C1; lia.
Qed.

(* dp's display string at a state of the piece: exp_dp ++ NUL in its heap block (inv_J_end, n_r = 0). *)
Lemma kd_dpstr : forall m md0, AR SEGS B ly2 S2 W2 m md0 -> kkeep B g pos mf ly2 S2 W2 mem2 m ->
  reac_box_catalogue_defect.catd_hpstr B ly2 S2 W2 m dp (SlotModel.n_EXP_DP (e_pl g)) /\
  4096 <= dp /\ dp + Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1 <= alloc_ceiling.
Proof.
intros m md0 HAR (_ & K2 & _).
pose proof HKH as (_ & _ & _ & _ & _ & _ & HHB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR0 & Hnr).
destruct HHB as [Hperm _].
assert (Hindp : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly2 S2)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. right. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 m md0 dp _ HAR Hindp) as (_ & Hdp4096 & Hdpceil & _).
destruct (KModel.n_r0 _ Hnr) as [Hwok Hfits].
pose proof (KModel.fits_unfold _ Hfits) as (_ & _ & Hld).
unfold SlotModel.n_ld in Hld.
set (sd := SlotModel.n_EXP_DP (e_pl g)) in *.
pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(lia)) as Hrq.
assert (Lzd : map (fun b : byte => bv_unsigned b) (sd ++ [RcIdentModel.zb 0]) = reac_box_catalogue_defect.catd_lz sd)
  by (unfold reac_box_catalogue_defect.catd_lz; rewrite map_app; reflexivity).
pose proof (proj2 (proj2 (HR0 Hnr))) as Hby. unfold bytes_at8 in Hby. rewrite Lzd in Hby.
split; [|clear - Hdp4096 Hdpceil Hrq Hld; split; lia].
split; [|split].
- apply (k_garr8_moved (w_H W2) (w_H W2) mem2 m dp _); [|exact Hby].
  intros k Hk. rewrite reac_box_catalogue_defect.catd_lz_len in Hk.
  apply (K2 dp _ k Hindp). clear - Hk Hld Hrq. lia.
- exact (KModel.nzb_notin sd (KModel.nzb_EXP_DP _ Hwok)).
- exists (Z.max (SlotModel.t_cap_disp (e_pl g)) 1). split; [exact Hindp | clear - Hld; lia].
Qed.

(* The strcmp wrapper at 0x82344 on (P, dp) (return +0x1bd4): its result is 0 iff the display string sP is exp_dp. *)
Lemma kd_strcmp : forall (regsT : bvmap 5 word) memT mdc (Q : world SEGS -> config -> Prop) (P : Z) (sP : list byte) (s0 M : Z),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 memT mdc (4 * Z.of_nat (m_nrec g) + 7) ->
  kkeep B g pos mf ly2 S2 W2 mem2 memT ->
  getr regsT 2 = w64 mf -> getr regsT 9 = w64 mf -> getr regsT 8 = w64 (e_sp0 g) ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 21 = w64 tk -> getr regsT 23 = w64 (shadow_addr (SFa g pos)) ->
  getr regsT 1 = Z_to_bv 64 (BASE + 0x1bd4) ->
  getr regsT 10 = w64 P -> getr regsT 11 = w64 dp ->
  getr regsT 19 = w64 s0 -> (s0 = 0 \/ s0 = 1) -> getr regsT 18 = w64 M ->
  M = s0 + (if bool_decide (sP = SlotModel.n_EXP_DP (e_pl g)) then 0 else 2) ->
  0 < P < 2 ^ 64 -> reac_box_catalogue_defect.catd_rostr G W2 memT P sP ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1bec) regs' mem' md') Q) ->
  SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_strcmp)) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros regsT memT mdc Q P sP s0 M HJ HKP Rsp Rs1 Rs0 Rgp Rtp Rtk Rsh Rra R10 R11 R19 Hs0 R18 HMv RP HSTR HQ.
pose proof GEOM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HART.
pose proof (k_gm _ _ _ _ _ _ HPRE) as GM. pose proof (k_iv _ _ _ _ _ _ HPRE) as IV.
destruct (kd_dpstr memT mdc HART HKP) as ((GD & ND & nd & Hind & Lnd) & Hdp4096 & Hdpceil).
set (sd := SlotModel.n_EXP_DP (e_pl g)) in *.
destruct HSTR as (GP & NP & (qP & zP & HqP & HqP1 & HqP2) & LoP & HiP).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS ly2 S2 W2 memT mdc dp nd HART Hind) as (_ & _ & Hdceil & _).
pose proof (req_size_pos nd ltac:(lia)) as Hrq.
destruct (reac_box_catalogue_defect.catd_k_le sP sd) as [KP KD].
destruct (reac_box_catalogue_defect.catd_k_spec sP sd NP ND) as (KS1 & KS2 & KS3).
assert (AVP : forall j, (j <= length sP)%nat ->
  aview SEGS (w_H W2) memT (P + Z.of_nat j) = Some (nth j (reac_box_catalogue_defect.catd_lz sP) 0))
  by (intros j Hj; apply reac_box_catalogue_defect.catd_garr8_aview; [exact GP | rewrite reac_box_catalogue_defect.catd_lz_len; lia]).
assert (AVD : forall j, (j <= length sd)%nat ->
  aview SEGS (w_H W2) memT (dp + Z.of_nat j) = Some (nth j (reac_box_catalogue_defect.catd_lz sd) 0))
  by (intros j Hj; apply reac_box_catalogue_defect.catd_garr8_aview; [exact GD | rewrite reac_box_catalogue_defect.catd_lz_len; lia]).
set (kk := reac_box_catalogue_defect.catd_k sP sd) in *.
assert (KPRE : forall i0, 0 <= i0 < Z.of_nat kk -> exists c, aview SEGS (w_H W2) memT (P + i0) = Some c /\
  aview SEGS (w_H W2) memT (dp + i0) = Some c /\ c <> 0).
{ intros i0 Hi0. destruct (KS1 (Z.to_nat i0) ltac:(lia)) as [Eq Nz].
  exists (nth (Z.to_nat i0) (reac_box_catalogue_defect.catd_lz sP) 0).
  replace (P + i0) with (P + Z.of_nat (Z.to_nat i0)) by lia. replace (dp + i0) with (dp + Z.of_nat (Z.to_nat i0)) by lia.
  split; [apply AVP; lia|]. split; [rewrite Eq; apply AVD; lia | exact Nz]. }
set (cx := nth kk (reac_box_catalogue_defect.catd_lz sP) 0) in *.
set (cy := nth kk (reac_box_catalogue_defect.catd_lz sd) 0) in *.
assert (Hvx : aview SEGS (w_H W2) memT (P + Z.of_nat kk) = Some cx) by (apply AVP; lia).
assert (Hvy : aview SEGS (w_H W2) memT (dp + Z.of_nat kk) = Some cy) by (apply AVD; lia).
assert (Hmeet : AStrcmpDef.str_meet SEGS W2 memT P dp (Z.of_nat kk) cx cy)
  by (unfold AStrcmpDef.str_meet; exact (conj (Nat2Z.is_nonneg kk) (conj KPRE (conj Hvx (conj Hvy KS2))))).
assert (Asp : spZ regsT = mf) by (unfold spZ; rewrite Rsp; apply unsigned_lit_small; clear - G1 G2 G3 C1; lia).
assert (SRCP : src_ok SEGS W2 regsT memT P (Z.of_nat kk + 1)).
{ intros a Ha. split; [replace a with (P + Z.of_nat (Z.to_nat (a - P))) by lia; rewrite AVP by lia; discriminate|].
  rewrite Asp, Hes. clear - Ha HiP LoP KP G1 C1. lia. }
assert (SRCD : src_ok SEGS W2 regsT memT dp (Z.of_nat kk + 1)).
{ intros a Ha. split; [replace a with (dp + Z.of_nat (Z.to_nat (a - dp))) by lia; rewrite AVD by lia; discriminate|].
  rewrite Asp, Hes. clear - Ha Hdpceil KD G1 C1. lia. }
destruct (ro_read_ok_glob SEGS B G ly2 S2 W2 memT mdc qP zP P (Z.of_nat kk + 1) GM HqP IV HART
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [RAP HULLP].
pose proof (range_addressable_of_block SEGS B LAWS ly2 S2 W2 memT mdc dp nd dp (Z.of_nat kk + 1) HART Hind
  ltac:(lia) ltac:(lia)) as RAD.
pose proof (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 memT mdc dp nd dp (Z.of_nat kk + 1) HART Hind
  ltac:(lia) ltac:(lia) ltac:(lia)) as HULLD.
pose proof (amem_range_of_block SEGS B LAWS ly2 S2 W2 memT mdc dp nd dp (Z.of_nat kk + 1) HART Hind
  ltac:(lia) ltac:(lia)) as AMD.
assert (AMP : amem_range P (Z.of_nat kk + 1)) by (unfold amem_range; left; rewrite C5; lia).
eapply SRr_bind.
{ eapply (k_strcmp_at _ _ _ _ _ _ HPRE W2 regsT memT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly2 S2 mdc (4 * Z.of_nat (m_nrec g) + 7) P dp (Z.of_nat kk) cx cy (mf - e_sp0 g)
    (Z_to_bv 64 (BASE + 0x1bd4)) HJ R10 R11).
  - clear - RP; lia.
  - clear - Hdp4096; lia.
  - clear - KP HiP LoP; lia.
  - clear - KP HiP LoP; lia.
  - clear - KD Hdpceil C1; lia.
  - rewrite Asp. clear; lia.
  - clear - G4 G6. Z.div_mod_to_equations. lia.
  - clear - G5 G2; lia.
  - unfold ESTACK. clear - G7; lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hmeet.
  - exact SRCP.
  - exact SRCD.
  - intros a Ha. unfold ESTACK. clear - Ha HiP LoP KP G1 C1. lia.
  - intros a Ha. unfold ESTACK. clear - Ha Hdpceil KD G1 C1. lia.
  - exact AMP.
  - exact AMD.
  - exact RAP.
  - exact HULLP.
  - exact RAD.
  - exact HULLD. }
cbv beta. intros W3 c3 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hres & Hfr & Hpres).
set (v := AStrcmpDef.strcmp_res cx cy) in *.
assert (Hv0 : v = 0 <-> sP = sd).
{ rewrite <- KS3. unfold v, AStrcmpDef.strcmp_res. fold cx cy. split.
  - destruct (Z.eqb_spec cx cy) as [E|E]; [intros _; exact E|]. destruct (cx <? cy); intros H; discriminate H.
  - intros E. rewrite E, Z.eqb_refl. reflexivity. }
assert (Rv : -1 <= v <= 1) by (unfold v, AStrcmpDef.strcmp_res; destruct (cx =? cy); [lia | destruct (cx <? cy); lia]).
pose proof (proj1 HJ4) as HAR4.
apply (kd_after regs4 mem4 md4 Q s0 (v mod 2 ^ 64) M HJ4).
- apply (kd_kkeep_win memT mem4 mdc HART HKP). intros a Ha Hw. apply Hfr; [exact Ha|].
  replace (e_sp0 g + (mf - e_sp0 g)) with mf by lia. unfold ESTACK. clear - Hw. lia.
- rewrite (kd_pres 2%bv regsT regs4 HP4 ltac:(clear; kd_cs)). exact Rsp.
- rewrite (kd_pres 9%bv regsT regs4 HP4 ltac:(clear; kd_cs)). exact Rs1.
- rewrite (kd_pres 8%bv regsT regs4 HP4 ltac:(clear; kd_cs)). exact Rs0.
- rewrite (kd_pres 3%bv regsT regs4 HP4 ltac:(clear; kd_cs)). exact Rgp.
- rewrite (kd_pres 4%bv regsT regs4 HP4 ltac:(clear; kd_cs)). exact Rtp.
- rewrite (kd_pres 21%bv regsT regs4 HP4 ltac:(clear; kd_cs)). exact Rtk.
- rewrite (kd_pres 23%bv regsT regs4 HP4 ltac:(clear; kd_cs)). exact Rsh.
- rewrite Hres. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by (clear; lia). reflexivity.
- apply Z.mod_pos_bound. clear; lia.
- rewrite (kd_pres 19%bv regsT regs4 HP4 ltac:(clear; kd_cs)). exact R19.
- exact Hs0.
- rewrite (kd_pres 18%bv regsT regs4 HP4 ltac:(clear; kd_cs)). exact R18.
- rewrite HMv. f_equal.
  assert (Ev : (v mod 2 ^ 64 =? 0) = (v =? 0)).
  { destruct (Z.eqb_spec v 0) as [E|E]; [rewrite E; reflexivity|].
    apply Z.eqb_neq. intros Hm. apply E. destruct (Z.eq_dec v (-1)) as [->|N1]; [vm_compute in Hm; discriminate Hm|].
    rewrite Z.mod_small in Hm by lia. exact Hm. }
  rewrite Ev.
  destruct (Z.eqb_spec v 0) as [E|E].
  + rewrite (reac_box_catalogue_defect.catd_bd_true sP sd (proj1 Hv0 E)). reflexivity.
  + rewrite (reac_box_catalogue_defect.catd_bd_false sP sd (fun H => E (proj2 Hv0 H))). reflexivity.
- exact HQ.
Qed.

Lemma kd_rostr_eq : forall m m' P sP, reac_box_catalogue_defect.catd_rostr G W2 m P sP ->
  (forall x, mrestrict (w_H W2) m' x = mrestrict (w_H W2) m x) -> reac_box_catalogue_defect.catd_rostr G W2 m' P sP.
Proof.
intros m m' P sP (HG & HN & HR) HM. split; [|exact (conj HN HR)].
apply (garr8_frame SEGS _ _ P _ HG). intros a _. unfold mbyte. rewrite HM. reflexivity.
Qed.

(* +0x1b38 .. +0x1be0 (0x822ac .. 0x82354): s2 = the callee's mask; s6 <> 0 (0x822b0); the alignment test of
   the row (0x822b8, e mod 8 = 0); I at e+16 against t_in (0x822d8), O at e+20 against t_out (0x822f4) with
   their ASan tests (0x822d0, 0x822ec: the row is a registered global); s3 = 0 or 1; P at e+8 (ASan 0x82334);
   P = 0 goes to the compare, P <> 0 calls the strcmp wrapper (kd_strcmp); the compare and the store (kd_tail). *)

Lemma kd_post : forall (regs3 : bvmap 5 word) mem3 md3 (Q : world SEGS -> config -> Prop) (CAT e I O P : Z) (sP : list byte),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem3 ->
  getr regs3 2 = w64 mf -> getr regs3 9 = w64 mf -> getr regs3 8 = w64 (e_sp0 g) ->
  getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
  getr regs3 21 = w64 tk -> getr regs3 23 = w64 (shadow_addr (SFa g pos)) ->
  getr regs3 20 = w64 e -> getr regs3 22 = w64 CAT ->
  getr regs3 19 = w64 (SlotModel.t_in (e_pl g)) -> getr regs3 24 = w64 (SlotModel.t_out (e_pl g)) ->
  getr regs3 10 = w64 (reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK e (SlotModel.t_in (e_pl g))
    (SlotModel.t_out (e_pl g)) dp I O P sP (SlotModel.n_EXP_DP (e_pl g))) ->
  0x8000 <= CAT <= IMG_TOP -> CAT mod 8 = 0 ->
  0x8000 <= e -> e + 24 <= IMG_TOP -> e mod 8 = 0 -> reac_box_catalogue_defect.catd_glob G (e + 8) 16 ->
  -2 ^ 31 <= I < 2 ^ 31 -> -2 ^ 31 <= O < 2 ^ 31 -> 0 <= P < 2 ^ 64 ->
  val_mem SEGS (rd W2 mem3) (e + 8) 8 P -> val_mem SEGS (rd W2 mem3) (e + 16) 4 I ->
  val_mem SEGS (rd W2 mem3) (e + 20) 4 O ->
  (P <> 0 -> reac_box_catalogue_defect.catd_rostr G W2 mem3 P sP) ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1bec) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1b38) regs3 mem3 md3) Q.
Proof.
intros regs3 mem3 md3 Q CAT e I O P sP HJ HKP Rsp Rs1 Rs0 Rgp Rtp Rtk Rsh R20 R22 R19 R24 R10
  HC0 HC8 He0 He1 He8 Hglob RI RO RP VP VI VO HSTR HQ.
pose proof GEOM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof HKH as (_ & HFR & _ & _ & _ & HEC & HHB & _ & _ & _ & _ & _ & _ & _ & V184 & _).
pose proof HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V168 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (SF := SFa g pos) in *. set (sh := shadow_addr SF) in *.
pose proof (proj1 HJ) as HAR3.
pose proof (k_gm _ _ _ _ _ _ HPRE) as GM.
assert (M168 : val_mem SEGS (rd W2 mem3) (mf + 168) 8 SHADOW_OFF) by (apply (VMHI mem3 _ 8 _ HKP); [clear; lia | clear - G1 G2 G3; lia | exact V168]).
assert (M184 : val_mem SEGS (rd W2 mem3) (mf + 184) 8 dp) by (apply (VMHI mem3 _ 8 _ HKP); [clear; lia | clear - G1 G2 G3; lia | exact V184]).
destruct HHB as [Hperm _].
assert (Hindp : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly2 S2)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. right. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 dp _ HAR3 Hindp) as (_ & Hdp4096 & Hdpceil & _).
pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(lia)) as Hrq.
assert (Hdp : 4096 <= dp < alloc_ceiling) by (clear - Hdp4096 Hdpceil Hrq; lia).
pose proof (Z.mod_pos_bound I (2 ^ 32) ltac:(lia)) as RIu. pose proof (Z.mod_pos_bound O (2 ^ 32) ltac:(lia)) as ROu.
(* the environment *)
remember (Eimg (Ereg regs3 [Z_to_bv 64 kd_SB; Z_to_bv 64 P; Z_to_bv 64 (I mod 2 ^ 32); Z_to_bv 64 (O mod 2 ^ 32);
  Z_to_bv 64 dp])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 kd_SB)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 P)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (I mod 2 ^ 32))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (O mod 2 ^ 32))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 dp)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 4)).
assert (ER : regs_ok E sr_atoms regs3) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 kd_SB; Z_to_bv 64 P; Z_to_bv 64 (I mod 2 ^ 32);
  Z_to_bv 64 (O mod 2 ^ 32); Z_to_bv 64 dp]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - G1 G2 G3 C1. lia. }
assert (U20 : bv_unsigned (ew E 20) = e).
{ rewrite (EE 20%nat 20%bv eq_refl), R20. apply unsigned_lit_small. clear - He0 He1. lia. }
assert (U22 : bv_unsigned (ew E 22) = CAT).
{ rewrite (EE 22%nat 22%bv eq_refl), R22. apply unsigned_lit_small. clear - HC0. lia. }
assert (U23 : bv_unsigned (ew E 23) = sh).
{ rewrite (EE 23%nat 23%bv eq_refl), Rsh. apply unsigned_lit_small. clear - G14 G15 C1. lia. }
assert (Ush : 0 <= sh /\ sh + 128 <= alloc_ceiling) by (split; assumption).
assert (HS : st_ok_pi SEGS VAL E kd_ss2
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + 0x1b38)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kd_ss2. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold kd_rmf2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - G1 C1; lia|]. split; [clear - G1 G2 G3; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) kd_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold kd_SB; lia | clear; lia | exact M168].
      * apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 36 0) dp);
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hdp C1; lia | clear; lia | exact M184].
    + unfold kd_rrow, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [clear - He0; lia|]. split; [clear - He1; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ e 8 8 (SOff 33 0) P);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - RP; lia | clear; lia | exact VP].
      * apply (chunk_ok_val SEGS E _ e 16 4 (SOff 34 0) (I mod 2 ^ 32));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - RIu; lia | clear; lia |].
        exact (reac_box_catalogue_defect.catd_val_mem_mod _ _ 4 I VI).
      * apply (chunk_ok_val SEGS E _ e 20 4 (SOff 35 0) (O mod 2 ^ 32));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - ROu; lia | clear; lia |].
        exact (reac_box_catalogue_defect.catd_val_mem_mod _ _ 4 O VO).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, kd_rmf2, kd_rrow.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20.
    split; [split; [|exact Logic.I] | split; [exact Logic.I | exact Logic.I]].
    right. clear - G1 He1 C1. lia.
  - unfold facts_ok, kd_facts2. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [| split; exact Logic.I].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, E34, E35, U20, U22, !unsigned_lit_small by (unfold kd_SB; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold kd_SB. repeat match goal with |- _ /\ _ => split end; first [exact He8 | exact HC8 | exact Logic.I | lia]. }
assert (SHOK : sh_ok SEGS kd_Bx kd_SH E (mrestrict (w_H W2) mem3)).
{ destruct Hglob as (q & z & Hqz & Hq1 & Hq2).
  pose proof (ro_usable_glob SEGS B G ly2 S2 W2 mem3 md3 q z (e + 8) 16 GM Hqz HAR3 Hq1 Hq2) as HRA.
  unfold sh_ok, kd_SH. constructor; [|constructor].
  eapply shent_ok_of_range; [exact HRA | | | | |].
  + unfold U, kd_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold kd_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U20.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + 0x1b38)) with (Z_to_bv 64 (BASE + 0x1b38)).
assert (HM : forall x : word, mrestrict (w_H W2) mem3 x = mrestrict (w_H W2) mem3 x) by (intros; reflexivity).
set (tin := SlotModel.t_in (e_pl g)) in *. set (tout := SlotModel.t_out (e_pl g)) in *.
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 1)) as Rtin.
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 2)) as Rtout.
change (SlotModel.inb (e_pl g) (SlotModel.cT (e_pl g) + 1)) with tin in Rtin.
change (SlotModel.inb (e_pl g) (SlotModel.cT (e_pl g) + 2)) with tout in Rtout.
assert (E19 : ew E 19 = Z_to_bv 64 tin) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E24 : ew E 24 = Z_to_bv 64 tout) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E10 : ew E 10 = w64 (reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK e tin tout dp I O P sP
  (SlotModel.n_EXP_DP (e_pl g)))) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (Rtin' : -2 ^ 31 <= tin < 2 ^ 31) by (clear - Rtin; lia).
assert (Rtout' : -2 ^ 31 <= tout < 2 ^ 31) by (clear - Rtout; lia).
assert (U0 : U E (SLit 0) = 0) by (rewrite U_lit; [reflexivity | clear; lia]).
assert (Ee0 : (e =? 0) = false) by (apply Z.eqb_neq; clear - He0; lia).
assert (Edp0 : (dp =? 0) = false) by (apply Z.eqb_neq; clear - Hdp; lia).
let rec go :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK kd_Bspan; [kd_awr_ro |];
  kd_upd;
  repeat match goal with
  | H : branch_taken _ (sv_denot ?Ex _) (sv_denot ?Ex _) = _ |- _ =>
    let X19 := fresh "X" in let X24 := fresh "X" in let X33 := fresh "X" in let X34 := fresh "X" in let X35 := fresh "X" in
    assert (X19 : ew Ex 19 = Z_to_bv 64 tin) by (cbn [ew ewset Nat.eqb]; exact E19);
    assert (X24 : ew Ex 24 = Z_to_bv 64 tout) by (cbn [ew ewset Nat.eqb]; exact E24);
    assert (X33 : ew Ex 33 = Z_to_bv 64 P) by (cbn [ew ewset Nat.eqb]; exact E33);
    assert (X34 : ew Ex 34 = Z_to_bv 64 (I mod 2 ^ 32)) by (cbn [ew ewset Nat.eqb]; exact E34);
    assert (X35 : ew Ex 35 = Z_to_bv 64 (O mod 2 ^ 32)) by (cbn [ew ewset Nat.eqb]; exact E35);
    rewrite ?branch_ne_U, ?branch_eq_U in H;
    rewrite ?(reac_box_catalogue_defect.catd_sext Ex 34 I X34 RI), ?(reac_box_catalogue_defect.catd_sext Ex 35 O X35 RO),
      ?(reac_box_catalogue_defect.catd_U_atom_mod Ex 19 tin X19), ?(reac_box_catalogue_defect.catd_U_atom_mod Ex 24 tout X24),
      ?(U_atom Ex 33 P X33 RP), ?(U_lit Ex 0 ltac:(clear; lia)) in H;
    rewrite ?(reac_box_catalogue_defect.catd_eqb32 I tin RI Rtin'), ?(reac_box_catalogue_defect.catd_eqb32 O tout RO Rtout') in H;
    rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in H;
    clear X19 X24 X33 X34 X35
  end;
  lazymatch goal with
  | HS' : st_ok _ _ (setpc ?ssx _) _ |- _ =>
    (* the strcmp wrapper at 0x82344: P <> 0 *)
    lazymatch goal with HP0 : (P =? 0) = false |- _ =>
    let P0 := fresh "P0" in assert (P0 : P <> 0) by (apply Z.eqb_neq; exact HP0);
    prreg HS' (10%bv : bv 5) Q10; prreg HS' (11%bv : bv 5) Q11; prreg HS' (1%bv : bv 5) Q1;
    prreg HS' (18%bv : bv 5) Q18; prreg HS' (19%bv : bv 5) Q19;
    prreg HS' (2%bv : bv 5) Q2; prreg HS' (9%bv : bv 5) Q9; prreg HS' (8%bv : bv 5) Q8;
    prreg HS' (3%bv : bv 5) Q3; prreg HS' (4%bv : bv 5) Q4; prreg HS' (21%bv : bv 5) Q21; prreg HS' (23%bv : bv 5) Q23;
    pmkst HS';
    eapply kd_strcmp;
    [ exact HJ
    | exact (kd_kkeep_eq mem3 _ HKP HM)
    | rewrite Q2, (EE 2%nat 2%bv eq_refl); exact Rsp
    | rewrite Q9, (EE 9%nat 9%bv eq_refl); exact Rs1
    | rewrite Q8, (EE 8%nat 8%bv eq_refl); exact Rs0
    | rewrite Q3, (EE 3%nat 3%bv eq_refl); exact Rgp
    | rewrite Q4, (EE 4%nat 4%bv eq_refl); exact Rtp
    | rewrite Q21, (EE 21%nat 21%bv eq_refl); exact Rtk
    | rewrite Q23, (EE 23%nat 23%bv eq_refl); exact Rsh
    | exact Q1
    | rewrite Q10; exact E33
    | rewrite Q11; exact E36
    | rewrite Q19; reflexivity
    | clear; lia
    | rewrite Q18; exact E10
    | unfold reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK; rewrite Ee0, Edp0, HP0;
      repeat match goal with H : (?x =? ?y) = ?b |- context [?x =? ?y] => rewrite H end;
      cbn [andb orb]; reflexivity
    | clear - RP P0; lia
    | exact (kd_rostr_eq mem3 _ P sP (HSTR P0) HM)
    | exact HQ ]
    end
  | HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
    let K := eval vm_compute in (run_K A_LIM kd_Bx kd_SH ss) in
    let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K kd_Bx kd_Bspan kd_SH (start K kd_Bx kd_Bspan kd_SH ss) end in
    let p := eval vm_compute in (ss_pc ss) in
    lazymatch why with
    | SR_branch _ _ _ =>
       lazymatch eval vm_compute in (p =? 0x1be0) with
       | true =>
         (* the compare with P = 0 *)
         lazymatch goal with HP0 : (P =? 0) = true |- _ =>
         prreg HS' (18%bv : bv 5) Q18; prreg HS' (19%bv : bv 5) Q19;
         prreg HS' (2%bv : bv 5) Q2; prreg HS' (9%bv : bv 5) Q9; prreg HS' (8%bv : bv 5) Q8;
         prreg HS' (3%bv : bv 5) Q3; prreg HS' (4%bv : bv 5) Q4; prreg HS' (21%bv : bv 5) Q21; prreg HS' (23%bv : bv 5) Q23;
         pmkst HS';
         apply kd_tail;
         [ exact HJ
         | exact (kd_kkeep_eq mem3 _ HKP HM)
         | rewrite Q2, (EE 2%nat 2%bv eq_refl); exact Rsp
         | rewrite Q9, (EE 9%nat 9%bv eq_refl); exact Rs1
         | rewrite Q8, (EE 8%nat 8%bv eq_refl); exact Rs0
         | rewrite Q3, (EE 3%nat 3%bv eq_refl); exact Rgp
         | rewrite Q4, (EE 4%nat 4%bv eq_refl); exact Rtp
         | rewrite Q21, (EE 21%nat 21%bv eq_refl); exact Rtk
         | rewrite Q23, (EE 23%nat 23%bv eq_refl); exact Rsh
         | rewrite Q18, Q19, E10; unfold w64; f_equal;
           unfold reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK; rewrite Ee0, Edp0, HP0;
           repeat match goal with H : (?x =? ?y) = ?b |- context [?x =? ?y] => rewrite H end;
           cbn [andb orb]; reflexivity
         | exact HQ ]
         end
       | false => psrr_branch_tok RUN BR HS' SHOK' kd_Bspan; [go | go]
       end
    | _ => idtac "STUCK" p why; fail
    end
  end end in go.
Qed.

(* What reac_box_catalogue_defect's own journal keeps of kkeep: everything but its stack window. *)
Lemma kd_kkeep_cj : forall memc mdc mem3 md3 sp1, sp1 = mf -> kkeep B g pos mf ly2 S2 W2 mem2 memc ->
  ajournal SEGS B reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK sp1 [] ly2 S2 W2 memc mdc []
    ly2 S2 W2 mem3 md3 0 ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem3.
Proof.
intros memc mdc mem3 md3 sp1 -> (K1 & K2 & K3) HJc.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
pose proof GEOM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
split; [|split].
- intros a Ha Hw. rewrite F1; [exact (K1 a Ha Hw) | exact Ha |].
  unfold reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK. exact Hw.
- intros b n i Hb Hi. rewrite (F2 b n i Hb Hb Hi); [exact (K2 b n i Hb Hi) | intros (r' & [] & _)].
- intros a Ha Hc Hs. rewrite (F4 4 pos a G16 Ha); [exact (K3 a Ha Hc Hs) | intros (r' & [] & _)].
Qed.

(* +0x1b38, the return of reac_box_catalogue_defect (called at 0x822a8 with the row e, t_in, t_out, dp): the
   row's I, O, P and display string sP that the call read at the call state memc. HSAME is the one fact this
   piece takes about the call beyond its contract: the bytes the inline mask reads again (the row's 16 bytes at
   e+8 and, when P <> 0, P's string with its NUL) read the same at the return state mem3 as at memc. *)
Lemma kd_ret : forall (regsc regs3 : bvmap 5 word) memc mdc mem3 md3 (Q : world SEGS -> config -> Prop)
  (I O P : Z) (sP : list byte),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) ->
  ajournal SEGS B reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK (e_sp0 g + (mf - e_sp0 g)) []
    ly2 S2 W2 memc mdc [] ly2 S2 W2 mem3 md3 0 ->
  kkeep B g pos mf ly2 S2 W2 mem2 memc ->
  aregs_preserved regsc regs3 ->
  getr regsc 2 = w64 mf -> getr regsc 9 = w64 mf -> getr regsc 8 = w64 (e_sp0 g) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 21 = w64 tk -> getr regsc 23 = w64 (shadow_addr (SFa g pos)) ->
  getr regsc 20 = w64 (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11)) ->
  getr regsc 22 = w64 (VAL reac_box_catalogue.CAT_OBJ) ->
  getr regsc 19 = w64 (SlotModel.t_in (e_pl g)) -> getr regsc 24 = w64 (SlotModel.t_out (e_pl g)) ->
  getr regs3 10 = w64 (reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK
    (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11))
    (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) dp I O P sP (SlotModel.n_EXP_DP (e_pl g))) ->
  0x8000 <= VAL reac_box_catalogue.CAT_OBJ -> VAL reac_box_catalogue.CAT_OBJ mod 8 = 0 ->
  VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11) + 24 <= IMG_TOP ->
  -2 ^ 31 <= I < 2 ^ 31 -> -2 ^ 31 <= O < 2 ^ 31 -> 0 <= P < 2 ^ 64 ->
  val_mem SEGS (rd W2 memc) (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11) + 8) 8 P ->
  val_mem SEGS (rd W2 memc) (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11) + 16) 4 I ->
  val_mem SEGS (rd W2 memc) (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11) + 20) 4 O ->
  (P <> 0 -> reac_box_catalogue_defect.catd_rostr G W2 memc P sP) ->
  (forall a, (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11) + 8 <= a <
              VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11) + 24 \/
              (P <> 0 /\ P <= a < P + Z.of_nat (length sP) + 1)) ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) memc a) ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1bec) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1b38) regs3 mem3 md3) Q.
Proof.
intros regsc regs3 memc mdc mem3 md3 Q I O P sP HJ3 HJcal HKP HP Rsp Rs1 Rs0 Rgp Rtp Rtk Rsh R20 R22 R19 R24 Hm
  HC0 HC8 Hhi RI RO RP VPc VIc VOc HSc HSAME HQ.
pose proof (Z.mod_pos_bound (SlotModel.t_row (e_pl g)) 11 ltac:(lia)) as Rr11.
set (r := SlotModel.t_row (e_pl g) mod 11) in *.
set (CAT := VAL reac_box_catalogue.CAT_OBJ) in *.
set (e := CAT + 296 * r) in *.
pose proof (k_gcat _ _ _ _ _ _ HPRE) as HGC. change (VAL (A_OBJ 28)) with CAT in HGC.
assert (Hglob : reac_box_catalogue_defect.catd_glob G (e + 8) 16)
  by (exists CAT, 3256; split; [exact HGC|]; unfold e; clear - Rr11; lia).
assert (He8 : e mod 8 = 0).
{ unfold e. clear - HC8. rewrite Z.add_mod by lia. rewrite HC8.
  replace (296 * r) with (8 * (37 * r)) by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
assert (VM : forall a (n : nat) v, (forall k, 0 <= k < Z.of_nat n -> e + 8 <= a + k < e + 24) ->
  val_mem SEGS (rd W2 memc) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v Ha Hv. apply (val_mem_kept SEGS (w_H W2) (w_H W2) memc mem3 a n v); [|exact Hv].
  intros k Hk. apply HSAME. left. exact (Ha k Hk). }
apply (kd_post regs3 mem3 md3 Q CAT e I O P sP HJ3).
- exact (kd_kkeep_cj memc mdc mem3 md3 (e_sp0 g + (mf - e_sp0 g)) ltac:(clear; lia) HKP HJcal).
- rewrite (kd_pres 2%bv regsc regs3 HP ltac:(clear; kd_cs)). exact Rsp.
- rewrite (kd_pres 9%bv regsc regs3 HP ltac:(clear; kd_cs)). exact Rs1.
- rewrite (kd_pres 8%bv regsc regs3 HP ltac:(clear; kd_cs)). exact Rs0.
- rewrite (kd_pres 3%bv regsc regs3 HP ltac:(clear; kd_cs)). exact Rgp.
- rewrite (kd_pres 4%bv regsc regs3 HP ltac:(clear; kd_cs)). exact Rtp.
- rewrite (kd_pres 21%bv regsc regs3 HP ltac:(clear; kd_cs)). exact Rtk.
- rewrite (kd_pres 23%bv regsc regs3 HP ltac:(clear; kd_cs)). exact Rsh.
- rewrite (kd_pres 20%bv regsc regs3 HP ltac:(clear; kd_cs)). exact R20.
- rewrite (kd_pres 22%bv regsc regs3 HP ltac:(clear; kd_cs)). exact R22.
- rewrite (kd_pres 19%bv regsc regs3 HP ltac:(clear; kd_cs)). exact R19.
- rewrite (kd_pres 24%bv regsc regs3 HP ltac:(clear; kd_cs)). exact R24.
- exact Hm.
- unfold e in Hhi. clear - HC0 Hhi Rr11. lia.
- exact HC8.
- unfold e. clear - HC0 Rr11. lia.
- exact Hhi.
- exact He8.
- exact Hglob.
- exact RI.
- exact RO.
- exact RP.
- apply (VM _ 8%nat P); [intros k Hk; cbn in Hk; clear - Hk; lia | exact VPc].
- apply (VM _ 4%nat I); [intros k Hk; cbn in Hk; clear - Hk; lia | exact VIc].
- apply (VM _ 4%nat O); [intros k Hk; cbn in Hk; clear - Hk; lia | exact VOc].
- intros HP0. destruct (HSc HP0) as (GP & HR).
  split; [|exact HR].
  apply (k_garr8_moved (w_H W2) (w_H W2) memc mem3 P _); [|exact GP].
  intros k Hk. rewrite reac_box_catalogue_defect.catd_lz_len in Hk.
  apply HSAME. right. split; [exact HP0 | clear - Hk; lia].
- exact HQ.
Qed.

(* The neutral step kd_ret takes, from the call's frame clause: the row's bytes and P's string are image bytes,
   below the callee's stack window [mf - 8208, mf). *)
Lemma kd_same_A : forall memc mem3 (e P : Z) (sP : list byte),
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (e_sp0 g + (mf - e_sp0 g) - reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK <= a < e_sp0 g + (mf - e_sp0 g)) ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) memc a) ->
  0 <= e -> e + 24 <= IMG_TOP -> (P <> 0 -> reac_box_catalogue_defect.catd_rostr G W2 memc P sP) ->
  forall a, (e + 8 <= a < e + 24 \/ (P <> 0 /\ P <= a < P + Z.of_nat (length sP) + 1)) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) memc a.
Proof.
intros memc mem3 e P sP HK He0 He1 HS a Ha.
pose proof GEOM as (G1 & _).
pose proof asan_consts as (C1 & _).
assert (Hlo : 0 <= a /\ a < IMG_TOP).
{ destruct Ha as [Ha | (HP0 & Ha)]; [clear - Ha He0 He1; lia|].
  destruct (HS HP0) as (_ & _ & _ & LoP & HiP). clear - Ha LoP HiP. lia. }
apply HK; [clear - Hlo; lia|]. unfold reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK.
clear - Hlo G1 C1. lia.
Qed.

(* The call of reac_box_catalogue_defect at 0x822a8 on the row of t_row: its premises at the call state, then
   kd_ret at the return. *)
Lemma kd_call : kd_defect_at_A -> forall (regsc : bvmap 5 word) memc mdc (Q : world SEGS -> config -> Prop),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 memc mdc (4 * Z.of_nat (m_nrec g) + 7) ->
  kkeep B g pos mf ly2 S2 W2 mem2 memc ->
  getr regsc 2 = w64 mf -> getr regsc 9 = w64 mf -> getr regsc 8 = w64 (e_sp0 g) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 21 = w64 tk -> getr regsc 23 = w64 (shadow_addr (SFa g pos)) ->
  getr regsc 1 = Z_to_bv 64 (BASE + 0x1b38) ->
  getr regsc 10 = w64 (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11)) ->
  getr regsc 11 = w64 (SlotModel.t_in (e_pl g)) -> getr regsc 12 = w64 (SlotModel.t_out (e_pl g)) ->
  getr regsc 13 = w64 dp ->
  getr regsc 20 = w64 (VAL reac_box_catalogue.CAT_OBJ + 296 * (SlotModel.t_row (e_pl g) mod 11)) ->
  getr regsc 22 = w64 (VAL reac_box_catalogue.CAT_OBJ) ->
  getr regsc 19 = w64 (SlotModel.t_in (e_pl g)) -> getr regsc 24 = w64 (SlotModel.t_out (e_pl g)) ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1bec) regs' mem' md') Q) ->
  SRr SEGS W2 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_reac_box_catalogue_defect)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros HKDA regsc memc mdc Q HJ HKP Rsp Rs1 Rs0 Rgp Rtp Rtk Rsh Rra R10 R11 R12 R13 R20 R22 R19 R24 HQ.
pose proof GEOM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 8)) as Rrow.
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 1)) as Rin.
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 2)) as Rout.
change (SlotModel.inb (e_pl g) (SlotModel.cT (e_pl g) + 8)) with (SlotModel.t_row (e_pl g)) in Rrow.
change (SlotModel.inb (e_pl g) (SlotModel.cT (e_pl g) + 1)) with (SlotModel.t_in (e_pl g)) in Rin.
change (SlotModel.inb (e_pl g) (SlotModel.cT (e_pl g) + 2)) with (SlotModel.t_out (e_pl g)) in Rout.
pose proof (Z.mod_pos_bound (SlotModel.t_row (e_pl g)) 11 ltac:(lia)) as Rr11.
pose proof (proj1 HJ) as HARc.
(* the image at the call state: the row of t_row *)
pose proof (k_aro B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH memc mdc HJ) as (HAPc & _).
pose proof (k_himg _ _ _ _ _ _ HPRE W2 memc HAPc) as HIMGc.
pose proof HIMGc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H28al & HROW).
change (VAL (A_OBJ 28)) with (VAL reac_box_catalogue.CAT_OBJ) in H28al, HROW.
pose proof (HROW 0 ltac:(unfold reac_box_catalogue.BOX_COUNT; lia)) as (H0lo & _).
destruct (HROW (SlotModel.t_row (e_pl g) mod 11) ltac:(unfold reac_box_catalogue.BOX_COUNT; lia)) as
  (Hlo & Hhi & Hs1 & Hs31 & I & O & P & sP & RI & RO & RP & VPc & VIc & VOc & HSc).
clear HROW.
set (r := SlotModel.t_row (e_pl g) mod 11) in *.
set (CAT := VAL reac_box_catalogue.CAT_OBJ) in *.
set (e := CAT + 296 * r) in *.
pose proof (k_gcat _ _ _ _ _ _ HPRE) as HGC. change (VAL (A_OBJ 28)) with CAT in HGC.
assert (Hglob : reac_box_catalogue_defect.catd_glob G (e + 8) 16)
  by (exists CAT, 3256; split; [exact HGC|]; unfold e; clear - Rr11; lia).
assert (He8 : e mod 8 = 0).
{ unfold e. clear - H28al. rewrite Z.add_mod by lia. rewrite H28al.
  replace (296 * r) with (8 * (37 * r)) by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
destruct (kd_dpstr memc mdc HARc HKP) as (HDP & Hdp4096 & Hdpceil).
destruct (k_achain B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH memc HKP) as (ch & Hch).
assert (Asp : spZ regsc = e_sp0 g + (mf - e_sp0 g))
  by (unfold spZ; rewrite Rsp; rewrite unsigned_lit_small by (clear - G1 G2 G3 C1; lia); clear; lia).
assert (As0 : s0Z regsc = e_sp0 g)
  by (unfold s0Z; rewrite Rs0; apply unsigned_lit_small; clear - G2 G3 G1 C1; lia).
eapply SRr_bind.
{ eapply (HKDA W2 regsc memc LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly2 S2 mdc (4 * Z.of_nat (m_nrec g) + 7) (mf - e_sp0 g) (Z_to_bv 64 (BASE + 0x1b38)) ch
    e (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) dp I O P sP (SlotModel.n_EXP_DP (e_pl g)) HJ Asp).
  - clear - G4 G6. Z.div_mod_to_equations. lia.
  - clear - G5 G2; lia.
  - unfold reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK. clear - G7; lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO; lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by (clear; lia). rewrite As0. exact Hch.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - clear - Hhi Hlo; lia.
  - clear - Rin; lia.
  - clear - Rout; lia.
  - clear - Hdp4096 Hdpceil C1; lia.
  - exact RI.
  - exact RO.
  - exact RP.
  - intros _. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hglob|]. split; [exact He8|].
    split; [exact Hs1|]. split; [exact Hs31|]. split; [exact VPc|]. split; [exact VIc | exact VOc].
  - intros _ _ HP0. split; [exact (HSc HP0) | exact HDP]. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJcal & HP & (Hm & -> & -> & -> & HKEEP)).
rewrite Z.add_0_r in HJ3.
change (Z_to_bv 64 (BASE + 0x1b38)) with (w64 (BASE + 0x1b38)).
apply (kd_ret regsc regs3 memc mdc mem3 md3 Q I O P sP HJ3 HJcal HKP HP Rsp Rs1 Rs0 Rgp Rtp Rtk Rsh R20 R22 R19 R24 Hm).
- clear - H0lo; lia.
- exact H28al.
- exact Hhi.
- exact RI.
- exact RO.
- exact RP.
- exact VPc.
- exact VIc.
- exact VOc.
- exact HSc.
- exact (kd_same_A memc mem3 e P sP HKEEP ltac:(clear - H0lo Rr11; unfold e; lia) Hhi HSc).
- exact HQ.
Qed.

(* The piece, given kd_defect_at_A: kd_pre to the call, kd_call. *)
Lemma kd_main : kd_defect_at_A -> forall regs mem md (Q : world SEGS -> config -> Prop),
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md -> getr regs 18 = w64 (SFa g pos + V_cnt) ->
  getr regs 10 = w64 (VAL reac_box_catalogue.CAT_OBJ) ->
  val_mem SEGS (rd W2 mem) (SFa g pos + V_cnt) 8 reac_box_catalogue.BOX_COUNT ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x1bec) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1ae8) regs mem md) Q.
Proof.
intros HKDA regs mem md Q HKC R18 R10 VC HQ.
apply (kd_pre regs mem md Q HKC R18 R10 VC).
intros regsc memc mdc HJc HKPc C2 C9 C8 C3 C4 C21 C23 C1 C10 C11 C12 C13 C20 C22 C19 C24.
exact (kd_call HKDA regsc memc mdc Q HJc HKPc C2 C9 C8 C3 C4 C21 C23 C1 C10 C11 C12 C13 C20 C22 C19 C24 HQ).
Qed.
End run.
End h.
(* k_def given the call's frame clause: when the callee's post and k_defect_at carry it, k_def is
   k_def_A (fun HPRE => k_defect_at ... HPRE). *)
Lemma k_def_A : (KPREn -> kd_defect_at_A) -> k_def_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS G.
Proof.
intros HA HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC R18 R10 VC HQ.
exact (kd_main HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (HA HPRE) regs mem md Q HKC R18 R10 VC HQ).
Qed.
End c.
End b.
End a.
