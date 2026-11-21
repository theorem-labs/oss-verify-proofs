(* reloc-zl14c e33e3d831484b4bbc5f9b09a789c1e85 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj InfATables IfA_base IfAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation ST := (fms SP Zs S D n OB osz lb la da gp tp FR fc).
  Notation INV m v0 v24 v48 v56 fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m v0 v24 v48 v56 sd id ni ai no ao msg mode hw bw fo).

  (* [comment removed for export] *)
  Definition at_latch (ci' co' hold' bits' : Z) : machine_state -> Prop :=
    fun ms' => exists (m' : amem) (x1 x6 x10 x11 x13 x15 x16 x21 v0 v24 v48 v56 : word) (fo' : Z -> Z),
      ms' = ST x1 x6 x10 x11 x13 x15 x16 x21 ci' co' hold' bits' 0x96e94 m' /\ INV m' v0 v24 v48 v56 fo'.

  Lemma if_lit : forall (m : amem) (v0 v24 v48 v56 : word) (fo : Z -> Z) (x1 x6 x10 x13 x15 x16 x21 : word) (ci co hold bits k : Z),
    INV m v0 v24 v48 v56 fo ->
    0 <= k < na -> code_val (rdL k) < 256 -> 0 <= co -> co + 258 <= osz ->
    evtF asegs RNG (at_latch ci (co + 1) hold bits)
      (ST x1 x6 x10 (Z_to_bv 64 (la + 4 * k)) x13 x15 x16 x21 ci co hold bits 0x96e60 m).
  Proof using All.
    intros until k. intros INV0 HK HV CO0 CO258.
    open_fctx CX. open_finv INV0. unfold fms, at_latch.
    clear ZSD WSZ WNX WIN TOKL TOKD SANE FWR WH WN BO0 DB LB Z0 ZL S0 SL D1 DL D8 PAYB PAYR PAYN UNP DJD DJP RD RSD
          TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2 SHZ DJZ SHS DJS RZ RSZ RS RSS.
    assert (TLC : bytes_at asegs m la (u32s (fws rdL (Z.to_nat na)))).
    { eapply bytes_at_transport; [exact TLB| exact MU|]. rewrite u32s_length, fws_length.
      replace (Z.of_nat (4 * Z.to_nat na)) with (4 * na) by lia. exact DJTL. }
    pose proof (TLR k HK) as RK. pose proof (code_val_range (rdL k)) as RCV.
    pose proof (code_read_val asegs m la (fws rdL (Z.to_nat na)) k (rdL k) TLC (f32arr_nth rdL (Z.to_nat na) k ltac:(lia)) ltac:(lia) RK) as RDV.
    zrunb [0x96e84]. rewrite zx16_small by lia. zs. zs.
    f8_open_at OUT co C EC CH CC.
    zs. (* [comment removed for export] *)
    f8_close_at CH CC EC (code_val (rdL k)) OUT'; [rewrite unsigned_lit by lia; reflexivity|].
    zs. subst C. setreg 17 (Z_to_bv 64 (OB + (co + 1))) ltac:(f_equal; lia).
    pose proof (fupd8_range fo co (code_val (rdL k)) osz FOR ltac:(lia)) as FOR'.
    apply evtF_done. eexists. do 12 eexists. exists (fupd8 fo co (code_val (rdL k))).
    split; [unfold fms; reflexivity|]. close_finv.
  Qed.
End P.
End CANSEC1.
