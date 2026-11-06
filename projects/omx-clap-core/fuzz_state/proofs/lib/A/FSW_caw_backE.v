(* check_as_written, the back of the walk as ONE lemma for the assembly: cawb_enter takes the hand-over state at 0x8197c
   (`jal __wrap_free` of six; cawb_xss, which is a Theorem Labs lane's FSW_caw_accept.v caa_xss verbatim, so the two are
   convertible) to check_as_written_spec's post (cawb_post). It is FSW_caw_back.v's cawb_to_mid (free (six), the
   branches 0x81980 .. 0x81994, bcmp 0x819a4, to cawb_mid at 0x819a8 / 0x819ac) followed by FSW_caw_epi.v's cawb_epi
   (the epilogue 0x819ac .. 0x819c8 and the tail free 0x819cc, a Theorem Labs lane).
   Atom 2 of E is the ENTRY sp: cawb_xss's frame region caw_stk is based at atom 2 (chunks at -48 .. -8) while the
   machine sp is entry sp - 48, so the epilogue's `ld ra, 0x28(sp)` reads entry sp - 8, caw_stk's last chunk (atom 1).
   Section hypotheses: FSW_caw_back.v's Section W, by name (B, IMG, FS_ENV, ML, RTb, RTf).
   Rule 24: no function is proved here; this file proves no *_spec. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w AF0l FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_malloc_free
FSW_caw_defs FSH_Fn_checks FSW_caw_back FSW_caw_epi.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis RTb : FSupoisonU.abcmp_realizesU tfibsegs B PC_bcmp.
Hypothesis RTf : pc_wrap_free (as_code B) = PC_free /\ FSupoisonU.afree_realizesU tfibsegs B.

Theorem cawb_enter : forall ly S U W0 regs mem md ch bd l (tb : list Z) live peak cnt fail E ms mdc lyc Sc W six want n,
  fpreU tfibsegs B STK_check_as_written ly S U W0 regs mem md ch -> fs_heads B ly S U ->
  getr regs 11 = w64 bd -> getr regs 12 = w64 l -> Z.of_nat (length tb) <= PRESET_FILE_MAX_BYTES ->
  caw_answerA tfibsegs B ly S U W0 mem tb bd l -> fs_glob tfibsegs W0 mem live peak cnt fail ->
  st_nev S + EV_check_as_written <= EV_MAX ->
  st_ok tfibsegs E cawb_xss (restrict (w_H W) ms) ->
  ew E 1 = getr regs 1 ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> ew E (Z.to_nat (bv_unsigned r)) = getr regs r) ->
  ew E 11 = getr regs 11 -> ew E 12 = getr regs 12 ->
  ew E 33 = Z_to_bv 64 six -> ew E 34 = Z_to_bv 64 want -> ew E 49 = Z_to_bv 64 n ->
  @ajournal rc SK tfibsegs B STK_check_as_written (spZ regs) [] ly S W0 (unpoison U mem) md [] lyc Sc W
    (unpoison U (ms_mem ms)) mdc 2 ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ablocks B lyc Sc = (ablocks B ly S ++ [(want, b64_alloc_bound (Z.of_nat (length tb)))]) ++
    [(six, Z.max (Z.of_nat (length tb)) 1)] ->
  (forall m, ~ In (want, m) (ablocks B ly S)) -> (forall m, ~ In (six, m) (ablocks B ly S)) ->
  (WriterSpec.b64_dec tb = None -> n = SIZE_MAXZ) ->
  (forall bs, WriterSpec.b64_dec tb = Some bs ->
     n = Z.of_nat (length bs) /\ n <= b64_alloc_bound (Z.of_nat (length tb)) /\ caw_bytes W (ms_mem ms) want bs) ->
  SRr tfibsegs W (mkCfg ms mdc) (cawb_post B regs ly S U W0 mem md live peak cnt fail).
Proof.
intros ly S U W0 regs mem md ch bd l tb live peak cnt fail E ms mdc lyc Sc W six want n
  HPRE FH H11 H12 Htb HANS HG Hev HS E1 ECS E11 E12 E33 E34 E49 HJ HARU Hab Hfw Hfs Hnone Hsome.
eapply SRr_bind.
{ exact (@cawb_to_mid fx rc SK B FS_ENV ML RTb RTf ly S U W0 regs mem md ch bd l tb E ms mdc lyc Sc W six want n
    HPRE FH H11 H12 Htb HANS Hev HS E1 ECS E11 E12 E33 E34 E49 HJ HARU Hab Hfw Hfs Hnone Hsome). }
cbv beta. intros W2 c2 _ (pc & Hpc & HM).
exact (@cawb_epi fx rc SK B IMG FS_ENV ML RTf regs ly S U W0 mem md ch live peak cnt fail want _ pc W2 c2
  HPRE FH HG Hev Hpc HM).
Qed.

End W.
