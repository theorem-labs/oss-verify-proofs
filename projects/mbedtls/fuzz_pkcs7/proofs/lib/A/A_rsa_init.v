(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT A_rt_facts A_x509_crt_init.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA LxSum.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt LxA_sums.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0071a61c3531aa3a 0 2 0 1 32 1P0177ec55bd83904c 0 5 0 1 31 1 34 1 39 1 40 1P096c78d634759243 0 2 0 1 2 1P0b4640c98b5e6eb8 0 4 1 1 2 1 41 1 42 1P0d88fcef0dc1c7fa 0 4 0 1 31 1 39 1 40 1P15859d6e9c0d8e83 0 5 0 1 31 1 34 1 39 1 40 1P18302c8baeea374b 0 5 0 1 33 1 36 1 41 1 42 1P18679ca32f47c6ef 0 2 0 1 32 1P1d25fa090d89a41d 0 4 1 1 2 1 41 1 42 1P1d43a3bc5c3a9012 0 6 0 1 2 1 33 1 36 1 41 1 42 1P1d82e8d623788a11 0 4 0 16 2 16 39 16 40 16P220ffa9027cfebe6 2 31 0 6 0 1 2 1 33 1 36 1 41 1 42 1 0 4 0 1 1 1 41 1 42 1P2da760ee206d23cb 1 1 16 2 0 1 39 1 3 3 1 40 1 41 16P355b8b46561ba4cf 0 5 0 1 33 1 36 1 41 1 42 1P366474b9502ad023 0 4 0 1 30 1 39 1 40 1P371bd42db347219d 0 4 0 1 30 1 39 1 40 1P38d29717abd24e10 0 5 0 1 31 1 34 1 39 1 40 1P3a824a2f18c4951e 0 5 0 1 31 1 34 1 39 1 40 1P3ba8ebb60050774a 0 6 0 1 31 1 32 1 34 1 39 1 40 1P3f6d773d6c811533 0 4 0 1 30 1 39 1 40 1N040a9eb42cc8482dN0623371d42a19d9cN06f33aeece02cfd7N0a2b5dd1aa2369f6N0ff51435577fbfddN1c687ff1d7c26007N1cedefb4ef97d59bN1d64f52d62d0db8aN1f1a3dfc97433406N203027e1de4a48aaN3282cda761c6aa19N34537a2485dd69e8N38bdb8bc4916704dN3b2a9833de863c61"%lxh.
Ltac2 gd_tbl_A_rsa_init () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.arl_amemset"; "OSSVerify.KrLib.A.A_x509_crt_init.A_AMEMSET_I"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.LibA.ARt.arl_need_amem"; "OSSVerify.KrLib.A.A_x509_crt_init.struct_init_stmtA"; "A_RSA_INIT"; "RSA_INIT_SIZE"].


Definition A_RSA_INIT : Z := 0x0b16b8.   (* [comment removed for export] *)
Definition RSA_INIT_SIZE : Z := 232.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis AMS : arl_amemset R = A_AMEMSET_I.
  Hypothesis NEED0 : 0 <= arl_need_amem R.

  Lemma A_rsa_init_walk : struct_init_stmtA asegs R HIA A_RSA_INIT RSA_INIT_SIZE.
  Proof.
    unfold struct_init_stmtA, A_RSA_INIT, RSA_INIT_SIZE.
    intros until junk. intros HH HB HA ST LOS SLO TOP SPA DS MI OA CWA ->.
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof alloc_ceiling_pos as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by lia.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| lia| lia]).
    pose proof (rw_cells_bound _ _ _ _ HB) as AB. cbn [cells_size csize Nat.add] in AB.
    assert (JL : length junk = Z.to_nat 232) by (destruct HB as [[WF _] _]; cbn in WF; destruct WF as [WF _]; exact WF).
    assert (AB' : 0 <= A /\ A + 232 <= 2^64) by lia. clear AB. rename AB' into AB.
    pose proof (munch_refl [(A, A + 232); (lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    lx_pre. lxr_pose. lxa_auto [SUM_amemsetA 232 4] [A].
    lx_pre. lx_run_tac (PLANS [] [] 40%N [SUM_amemsetA 232 4]). lx_tree.
    all: lxr_leaf; lx_leaf.
  Qed.

End Walk.

Lemma A_rsa_init_spec : ltac2:(CDefT.buildp (gd_tbl_A_rsa_init ()) "PR,$0.PHIA,(1.$2.R1.)P,(3.(4.R2.))P,(5.$6.(7.R3.)$8.)P,(9.=(:.R4.))(;.$2.R5.R4.$<.$=.)")
(* [comment removed for export] *).
Proof. intros. eapply A_rsa_init_walk; eauto. Qed.
