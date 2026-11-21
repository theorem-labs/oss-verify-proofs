(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U Require Import TBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition L_CL_DONE : Z := 90232.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition s_regs_clh (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kS1 = c_u cx /\ zget_l Rb l kRA = 16209 /\
  s_vars cx st Rb l.

Definition clhead_stmt {RCa1 : RunCtx}  : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = CODELENS -> sinv cx st lf cf ->
    s_regs_clh cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CODELENS (zupd Rb l) M MD) T.

(* [comment removed for export] *)
Definition s_regs_cld (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kS1 = c_u cx /\ zget_l Rb l kRA = 16209 /\
  s_vars cx st Rb l /\ zget_l Rb l kA2 = t_nlen st /\ zget_l Rb l kA1 = t_nlen st + t_ndist st.

Definition cldone_stmt {RCa1 : RunCtx}  : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = CODELENS -> t_nlen st + t_ndist st <= t_shave st -> sinv cx st lf cf ->
    s_regs_cld cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_DONE (zupd Rb l) M MD) T.

Definition lenu_stmt {RCa1 : RunCtx}  : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = LEN_ -> sinv cx st lf cf ->
    s_regs_disp cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEN_ (zupd Rb l) M MD) T.
