(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow ExecF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr IfAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import U2AObj IfA_base IfAKit IfA_head IfA_declen IfA_lit IfA_lenb IfA_decdist IfA_distb IfA_direct IfA_win IfA_wcopy IfA_wcase IfA_wwrap IfA_err.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation ST := (fms SP Zs S D n OB osz lb la da gp tp FR fc).
  Notation LST := (lst FR fc gp tp SP Zs S D n OB osz lb la da).
  Notation INV m v0 v24 v48 v56 fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo).
  Notation LINV m v0 v24 fo := (INV m v0 v24 (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24)) fo).
  Notation AT_LATCH := (at_latch FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao msg mode hw bw).
  Notation ERR_POST := (err_post FR fc gp tp SP Zs S D n OB osz Wd wsz whave wnext lb db la da bo m1 sd id ni ai no ao hw bw).
  Notation K7 L := (L RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 CX).
  Notation K8 L := (L RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao msg mode hw bw CX).
  Notation KE L := (L RNG FR fc gp tp SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id ni ai no ao hw bw CX).

  (* [comment removed for export] *)
  Definition iter_post (ci co A Q : Z) : machine_state -> Prop :=
    fun ms' => exists ci' co' hold' bits' : Z,
      ci <= ci' <= n /\ co <= co' <= osz /\ 0 <= bits' <= 40 /\ 0 <= hold' < 2 ^ bits'
      /\ 8 * (n - ci') + bits' <= A /\ Q <= 8 * ci' - bits'
      /\ (AT_LATCH ci' co' hold' bits' ms' \/ ERR_POST ci' co' hold' bits' ms').

  (* [comment removed for export] *)
  Lemma if_iter_dist : forall (m : amem) (v0 v24 : word) (fo : Z -> Z) (x1 x6 x10 x15 x16 x21 : word) (len ci co hold bits k ci0 A Q : Z),
    LINV m v0 v24 fo ->
    0 <= k < nd -> 16 <= code_op (rdD k) <= 29 -> 1 <= code_val (rdD k) -> code_val (rdD k) + 2 ^ (code_op (rdD k) - 16) - 1 <= 32768 ->
    3 <= len <= 258 -> 0 <= ci0 <= ci -> ci <= n -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 13 <= 8 * (n - ci) + bits ->
    bo <= co -> co + 258 <= osz -> 8 * (n - ci) + bits <= A -> Q <= 8 * ci - bits ->
    evtF asegs RNG (iter_post ci0 co A Q)
      (LST x1 x6 x10 (Z_to_bv 64 (da + 4 * k)) (Z_to_bv 64 (code_op (rdD k))) x15 x16 x21 len ci co hold bits 0x96cd0 m).
  Proof using All.
    intros until Q. intros INV0 HK HOP HV1 HV LEN CI0 CIN BITS HOLD HA BCO CO258 AB QB.
    open_fctx CX.
    eapply evtF_cut.
    { eapply (K8 if_distb m v0 v24 fo x1 x6 x10 x15 x16 x21 len ci co hold bits k INV0); lia. }
    cbv beta. intros ms2 (m2 & y1 & y6 & y13 & y16 & y21 & w0 & dist & ci2 & hold2 & bits2 & INV2 & DIST & CI2 & BITS2 & HOLD2 & A2 & Q2 & CIN2 & CASE).
    destruct CASE as [[-> DCO] | [-> DCO]].
    - (* [comment removed for export] *)
      eapply evtF_mono.
      { eapply (K8 if_direct m2 w0 fo y1 y6 _ y13 y16 y21 len dist ci2 co hold2 bits2 INV2); lia. }
      cbv beta. intros ms3 HL. exists ci2, (co + len), hold2, bits2.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left. exact HL.
    - (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (K8 if_wentry m2 w0 fo y1 y6 (Z_to_bv 64 0) y13 y16 y21 len dist ci2 co hold2 bits2 INV2); lia. }
      cbv beta. intros ms3 (z1 & z6 & z10 & z11 & z15 & z16 & z21 & op & EOP & CASE).
      destruct CASE as [[-> TOO] | [[-> (OPW & WN0)] | [[-> (OPW & WNO)] | [-> (OPW & WNO)]]]].
      + eapply evtF_mono.
        { eapply (KE if_toofar m2 w0 msg mode fo z1 z6 z10 z11 z15 z16 z21 len dist op ci2 co hold2 bits2 INV2). }
        cbv beta. intros ms4 HE. exists ci2, co, hold2, bits2.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exact HE.
      + assert (WNZ : wsz <> 0) by lia.
        eapply evtF_mono.
        { eapply (K8 if_w0 WNZ m2 w0 fo z1 z6 z10 z15 z16 z21 len dist op ci2 co hold2 bits2 INV2); lia. }
        cbv beta. intros ms4 HL. exists ci2, (co + len), hold2, bits2.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left. exact HL.
      + assert (WNZ : wsz <> 0) by lia.
        eapply evtF_mono.
        { eapply (K8 if_wc WNZ m2 w0 fo z6 z10 z15 z16 z21 len dist op ci2 co hold2 bits2 INV2); lia. }
        cbv beta. intros ms4 HL. exists ci2, (co + len), hold2, bits2.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left. exact HL.
      + assert (WNZ : wsz <> 0) by lia.
        eapply evtF_mono.
        { eapply (K8 if_ww WNZ m2 w0 fo z6 z10 z15 z16 z21 len dist op ci2 co hold2 bits2 INV2); lia. }
        cbv beta. intros ms4 HL. exists ci2, (co + len), hold2, bits2.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left. exact HL.
  Qed.

  (* [comment removed for export] *)
  Lemma if_iter_len : forall (m : amem) (v0 v24 v48 v56 : word) (fo : Z -> Z) (x1 x6 x10 x15 x16 x21 : word) (ci co hold bits k ci0 A Q : Z),
    INV m v0 v24 v48 v56 fo ->
    0 <= k < na -> 16 <= code_op (rdL k) <= 21 -> 3 <= code_val (rdL k) -> code_val (rdL k) + 2 ^ (code_op (rdL k) - 16) - 1 <= 258 ->
    0 <= ci0 <= ci -> ci <= n -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 33 <= 8 * (n - ci) + bits ->
    bo <= co -> co + 258 <= osz -> 8 * (n - ci) + bits <= A -> Q <= 8 * ci - bits ->
    evtF asegs RNG (iter_post ci0 co A Q)
      (ST x1 x6 x10 (Z_to_bv 64 (la + 4 * k)) (Z_to_bv 64 (code_op (rdL k))) x15 x16 x21 ci co hold bits 0x96b40 m).
  Proof using All.
    intros until Q. intros INV0 HK HOP HV3 HV CI0 CIN BITS HOLD HA BCO CO258 AB QB.
    open_fctx CX.
    eapply evtF_cut.
    { eapply (K8 if_lenx m v0 v24 v48 v56 fo x1 x6 x10 x15 x16 x21 ci co hold bits k INV0); lia. }
    cbv beta. intros ms2 (m2 & y1 & y6 & y10 & y11 & y13 & y15 & y16 & y21 & w0 & w24 & len & ci2 & hold2 & bits2 & -> & INV2 & LEN & CI2 & BITS2 & HOLD2 & A2 & A2' & Q2 & CIN2).
    eapply evtF_cut.
    { eapply (K8 if_pull2d m2 w0 w24 fo y1 y6 y10 y11 y13 y15 y16 y21 len ci2 co hold2 bits2 INV2); lia. }
    cbv beta. intros ms3 (z1 & z6 & z10 & z11 & z13 & z15 & z16 & z21 & ci3 & hold3 & bits3 & -> & CI3 & BITS3 & HOLD3 & A3 & Q3 & CIN3).
    eapply evtF_cut.
    { eapply (K8 if_decdist m2 w0 w24 fo z1 z6 z10 z11 z13 z15 z16 z21 len ci3 co hold3 bits3 INV2); lia. }
    cbv beta. intros ms4 (u1 & u6 & u10 & u11 & u13 & u15 & u16 & u21 & hold4 & bits4 & BITS4 & DROP4 & HOLD4 & CASE).
    destruct CASE as [(kd & -> & _ & _ & HKD & HOPD & HVD1 & HVD) | ->].
    - eapply (if_iter_dist m2 w0 w24 fo u1 u6 u10 u15 u16 u21 len ci3 co hold4 bits4 kd ci0 A Q INV2); lia.
    - eapply evtF_mono.
      { eapply (KE if_baddist m2 w0 w24 msg mode fo u1 u6 u10 u11 u13 u15 u16 u21 len ci3 co hold4 bits4 INV2). }
      cbv beta. intros ms5 HE. exists ci3, co, hold4, bits4.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exact HE.
  Qed.

  (* [comment removed for export] *)
  Lemma if_iter : forall (m : amem) (v0 v24 v48 v56 : word) (fo : Z -> Z) (x1 x6 x10 x11 x13 x15 x16 x21 : word) (ci co hold bits : Z),
    INV m v0 v24 v48 v56 fo ->
    0 <= ci -> ci + 6 <= n -> 0 <= bits <= 40 -> bits <= 8 * ci -> 0 <= hold < 2 ^ bits -> bo <= co -> co + 258 <= osz ->
    evtF asegs RNG (iter_post ci co (8 * (n - ci) + bits - 1) (8 * ci - bits))
      (ST x1 x6 x10 x11 x13 x15 x16 x21 ci co hold bits 0x969d4 m).
  Proof using All.
    intros until bits. intros INV0 CI0 CI6 BITS B8 HOLD BCO CO258.
    open_fctx CX.
    eapply evtF_cut.
    { eapply (K7 if_head m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo x1 x6 x10 x11 x13 x15 x16 x21 ci co hold bits INV0); lia. }
    cbv beta. intros ms2 (y1 & y6 & y10 & y11 & y13 & y15 & y16 & y21 & ci2 & hold2 & bits2 & -> & CI2 & BITS2 & B82 & HOLD2 & A2).
    eapply evtF_cut.
    { eapply (K7 if_declen m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo y1 y6 y10 y11 y13 y15 y16 y21 ci2 co hold2 bits2 INV0); lia. }
    cbv beta. intros ms3 (z1 & z6 & z10 & z13 & z15 & z16 & z21 & k & hold3 & bits3 & HK & BITS3 & DROP3 & HOLD3 & CASE).
    destruct CASE as [[-> HV] | [[-> (HOP & HV3 & HV)] | (op & -> & OPR)]].
    - (* [comment removed for export] *)
      eapply evtF_mono.
      { eapply (K8 if_lit m v0 v24 v48 v56 fo z1 z6 z10 z13 z15 z16 z21 ci2 co hold3 bits3 k INV0); lia. }
      cbv beta. intros ms4 HL. exists ci2, (co + 1), hold3, bits3.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left. exact HL.
    - (* [comment removed for export] *)
      eapply (if_iter_len m v0 v24 v48 v56 fo z1 z6 z10 z15 z16 z21 ci2 co hold3 bits3 k ci _ _ INV0); lia.
    - (* [comment removed for export] *)
      eapply evtF_mono.
      { eapply (KE if_eob m v0 v24 v48 v56 msg mode fo z1 z6 z10 (Z_to_bv 64 (la + 4 * k)) z15 z16 z21 op ci2 co hold3 bits3 INV0 OPR). }
      cbv beta. intros ms4 HE. exists ci2, co, hold3, bits3.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exact HE.
  Qed.
End P.
End CANSEC1.
