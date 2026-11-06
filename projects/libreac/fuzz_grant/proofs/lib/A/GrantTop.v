(* The closing file of libreac/fuzz_grant's ASan build (image A): the two statements
   `Statements.asan_agrees` and `Statements.asan_halts`, with no hypothesis left.

   The chain, each link proved in its owner's file:
     GrantLibXClosed.grant_lib_x_all   (lib/A/Prog/GrantLibXClosed.v) -- the ASan build's
       program contract of the target's entry function (LLVMFuzzerTestOneInput, 0x806b0)
       and the functions it reaches, from the twelve closed phases of the entry walk; it
       takes reac_grant_build_sweep's contract, which `grant_BSW` below gives;
     AGrantT.grant_TFIB_T_of_lib       (lib/A/AGrantT.v) -- the driver and the start-up
       over that contract, giving GrantTFIB.TFIB_T;
     AsanTop.grant_asan_agrees_of_tfib / grant_asan_halts_of_tfib (lib/A/AsanTop.v) --
       the two statements from TFIB_T.

   Every walk this file names is applied at GrantB and the image instance PI_grant to
   GrantClose.v's closing instances; no statement is restated here.

   THE SINK INSTANCE IS EXPLICIT. lib/A/AsanTop.v loads the plain build's
   lib/Reusable/YI5b.v, which declares `#[global] Instance src0_sink_head` (the PLAIN
   build's output head), and lib/Reusable/YI5c.v, which declares `src0_sink`. Both hints
   are removed below, and every part this file names passes
   `SK := AE2k.tfib_sink_head` (the ASan image's own head) by name, so that a green build
   cannot be a vacuous one: a contract about the plain build's sink would prove nothing
   about fuzz_grant.asan. `sk_probe_is_asan` shows what a bare `sink_head` now resolves
   to. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_grant Require Statements.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YM05 YI16 YCbp.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AD2l AE2k ACfn GrantShape GrantTFIB.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal
GrantSyms GrantList GrantPa GrantImg GrantEntryDefs GrantEntryChain GrantBuildSweep GrantLibX
GrantCloseChk GrantClose.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require
CtrlLayBlockSpec CtrlLayBlock CtrlFinish CtrlStampHeadampSpec CtrlStampHeadamp
CtrlBuildGrantSweepSpec CtrlBuildGrantSweep HeadampTxEffective GrantBuildSweepWalk.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require GrantLibXClosed.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require AGrantT AsanTop.
Import ListNotations.
Open Scope Z_scope.

(* The guard: the plain build's sink hints are out of the way, so no `{SK}` of a walk or
   of a contract can be filled with the plain build's head. *)
#[local] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints YI5c.src0_sink : typeclass_instances.

(* What a bare `sink_head` resolves to in this file: the ASan image's own head. *)
Definition sk_probe : YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = AE2k.tfib_sink_head.
Proof. reflexivity. Qed.

(* ---- reac_grant_build_sweep's walk and its callees, at GrantB and PI_grant ----------
   reac_grant_build_sweep calls reac_headamp_tx_effective and reac_ctrl_build_grant_sweep;
   reac_ctrl_build_grant_sweep calls reac_ctrl_stamp_headamp, which calls ctrl_lay_block
   and ctrl_finish. Each walk's Section hypotheses (TLAY, TCF, TSTAMP, TEFF, TBGS and the
   runtime and image facts) are discharged here by the callee's walk and by GrantClose.v's
   instances, matched by statement. *)
Ltac grant_close :=
  first [ exact grant_LAWS | exact grant_PALib | exact grant_PALibF | exact grant_ML
        | exact grant_SMP | exact grant_FFL | exact grant_ASF
        | exact grant_AMEMSET | exact grant_AMEMCPY
        | exact grant_ASM0 | exact grant_ASM1 | exact grant_ASM2 | exact grant_ASM4
        | exact grant_img_shadow_vis | exact grant_RO
        | exact grant_rng_TMPL | exact grant_jt_eq | exact grant_je_rng
        | exact grant_rng_ROW | exact grant_rng_JT | exact grant_row_jt
        | exact grant_row_k | exact grant_row_tm | exact grant_row_ao | exact grant_row_al
        | exact grant_jt_e | exact grant_tbl_TMPL
        | exact grant_zs_ROW | exact grant_zs_TMPL | exact grant_zs_JT
        | exact grant_cf_gotimg | exact grant_cf_celimg | exact grant_cf_rowimg
        | exact grant_cf_rowsep | exact grant_cf_row
        | exact grant_globs_marked
        | exact grant_tbl_GRANT_HEAD_ACK | exact grant_tbl_GRANT_HEAD_MARK | exact grant_tbl_GROUPB
        | exact grant_rng_GRANT_HEAD_ACK | exact grant_rng_GRANT_HEAD_MARK | exact grant_rng_GROUPB
        | exact grant_glob_GRANT_HEAD_ACK | exact grant_glob_GRANT_HEAD_MARK
        | exact grant_glob_GROUPB ].

(* TLAY (CtrlStampHeadamp.v:93): ctrl_lay_block's walk, CtrlLayBlock.v:396. *)
Lemma grant_TLAY : forall (rcx : YM05.RunCeil) (fx : YK11.FPState),
  CtrlLayBlockSpec.tctrl_lay_block_spec (fx := fx) (rc := rcx) (SK := AE2k.tfib_sink_head)
    (PI := PI_grant) GrantB (pa_val (PAImg := PI_grant) A_TEXT + AF_ctrl_lay_block)
    (pa_relro_lo (PAImg := PI_grant)) (pa_relro_hi (PAImg := PI_grant)).
Proof. intros rcx fx. eapply CtrlLayBlock.pb_ctrl_lay_block; grant_close. Qed.

(* TCF (CtrlStampHeadamp.v:94): ctrl_finish's walk, CtrlFinish.v:493. *)
Lemma grant_TCF : forall (rcx : YM05.RunCeil) (fx : YK11.FPState),
  CtrlFinish.tctrl_finish_spec (fx := fx) (rc := rcx) (SK := AE2k.tfib_sink_head)
    (PI := PI_grant) GrantB (pa_val (PAImg := PI_grant) A_TEXT + AF_ctrl_finish)
    (pa_relro_lo (PAImg := PI_grant)) (pa_relro_hi (PAImg := PI_grant)).
Proof. intros rcx fx. eapply CtrlFinish.pb_ctrl_finish; grant_close. Qed.

(* TSTAMP (CtrlBuildGrantSweep.v:100): reac_ctrl_stamp_headamp's walk,
   CtrlStampHeadamp.v:825, at TLAY and TCF. *)
Lemma grant_TSTAMP : forall (rcx : YM05.RunCeil) (fx : YK11.FPState),
  CtrlStampHeadampSpec.tctrl_stamp_headamp_spec (fx := fx) (rc := rcx) (SK := AE2k.tfib_sink_head)
    (PI := PI_grant) GrantB (pa_val (PAImg := PI_grant) A_TEXT + AF_reac_ctrl_stamp_headamp)
    (pa_relro_lo (PAImg := PI_grant)) (pa_relro_hi (PAImg := PI_grant)).
Proof.
  intros rcx fx. eapply CtrlStampHeadamp.pb_reac_ctrl_stamp_headamp;
    first [ exact (grant_TLAY rcx fx) | exact (grant_TCF rcx fx) | grant_close ].
Qed.

(* The contract reac_grant_build_sweep's walk takes for its callee: reac_ctrl_build_grant_sweep's
   walk, CtrlBuildGrantSweep.v:1744, at TSTAMP and the image's registered globals. *)
Lemma grant_TBGS : forall (rcx : YM05.RunCeil) (fx : YK11.FPState),
  CtrlBuildGrantSweepSpec.tctrl_build_grant_sweep_spec (fx := fx) (rc := rcx) (SK := AE2k.tfib_sink_head)
    (PI := PI_grant) GrantB (pa_val (PAImg := PI_grant) A_TEXT + AF_reac_ctrl_build_grant_sweep)
    (pa_relro_lo (PAImg := PI_grant)) (pa_relro_hi (PAImg := PI_grant)).
Proof.
  intros rcx fx. eapply CtrlBuildGrantSweep.pb_reac_ctrl_build_grant_sweep;
    first [ exact (grant_TSTAMP rcx fx) | grant_close ].
Qed.

(* reac_headamp_tx_effective's walk (HeadampTxEffective.v:477), the other function
   reac_grant_build_sweep calls. *)
Lemma grant_TEFF : forall (rcx : YM05.RunCeil) (fx : YK11.FPState),
  HeadampTxEffective.theadamp_tx_effective_spec (fx := fx) (rc := rcx) (SK := AE2k.tfib_sink_head)
    (PI := PI_grant) GrantB.
Proof. intros rcx fx. eapply HeadampTxEffective.pb_headamp_tx_effective; grant_close. Qed.

(* reac_grant_build_sweep's walk (GrantBuildSweepWalk.v:276), at the two contracts above:
   the contract GrantLibXClosed.grant_lib_x_all takes. *)
Lemma grant_BSW : forall (rcx : YM05.RunCeil) (fx : YK11.FPState),
  treac_grant_build_sweep_spec (fx := fx) (rc := rcx) (SK := AE2k.tfib_sink_head)
    (PI := PI_grant) GrantB.
Proof.
  intros rcx fx. eapply GrantBuildSweepWalk.pb_reac_grant_build_sweep;
    first [ exact (grant_TEFF rcx fx) | exact (grant_TBGS rcx fx) | grant_close ].
Qed.

(* ---- the chain, with no hypothesis -------------------------------------------------- *)

(* A Section that declares no variable: `About` / `Check` after its `End` would show any
   Section variable that became an argument. *)
Section asan.

(* The ASan build's program contract: a Theorem Labs lane's twelve closed phases
   (lib/A/Prog/GrantLibXClosed.v:236) at reac_grant_build_sweep's closed walk. *)
Lemma grant_lib_all : forall rcx : YM05.RunCeil,
  @tfib_lib_contract_x_all rcx grant_shape GrantB ameter_triv GX_XL0 GX_XL0 GX_RLO GX_RHI.
Proof. intros rcx. apply (@GrantLibXClosed.grant_lib_x_all rcx); exact (grant_BSW rcx). Qed.

(* The driver and the start-up over that contract (lib/A/AGrantT.v:83). *)
Theorem grant_TFIB_T_of_parts : TFIB_T.
Proof. exact (AGrantT.grant_TFIB_T_of_lib grant_lib_all). Qed.

(* The two statements of libreac/fuzz_grant's ASan build (lib/A/AsanTop.v:103 and :119). *)
Theorem grant_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (AsanTop.grant_asan_agrees_of_tfib grant_TFIB_T_of_parts). Qed.
Theorem grant_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (AsanTop.grant_asan_halts_of_tfib grant_TFIB_T_of_parts). Qed.
End asan.

(* The acceptance: `About` and `Check` print each statement with NO leading argument. The
   statements' axioms are printed by the acceptance check (`ossv-vm check` / oft check), one
   `Print Assumptions` per statement; they are not printed here, because each one costs
   510-620 s (measured 2026-10-29, the four of them 99% of this file's build). *)
About grant_asan_agrees_of_parts.
Check grant_asan_agrees_of_parts.
About grant_asan_halts_of_parts.
Check grant_asan_halts_of_parts.
