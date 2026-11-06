(* fs program part, runtime half over fs.asan: fields of lib/A/FSH_Rt.v's FsRt, each proved at segs := tfibsegs and
   B := TfibB (lib/A/AD2l.v:15) and stated as the field is: fr_strlen (A3), fr_memchr (A5), fr_bcmp (A7), fr_memcpy (A8),
   fr_memset (A9) and fr_set_shadow_f5 (A10). Each theorem below has the type of the closing side's named runtime
   hypothesis (H_strlen / H_memchr / H_bcmp / H_memcpy / H_memset / H_set_shadow_f5, S0 8fee0cc526f lib/A/FSClose.v:162,
   :166, :170, :172, :174, :176-177, at its Local Abbreviation B := TfibB), so that side can apply it in place of that
   hypothesis.
   rule 24: no function proved (kind: merge). This file only instantiates proved theorems at TfibB and rewrites one pc:
   - A7: lib/A/FSupoisonCmp.v:35 tfib_abcmp_realizesU_closed (a Theorem Labs lane, POISON-U, a working branch
     cd7610bc4ed; it and its five walk files taken by path), stated at pc_wrap_bcmp (as_code B); pc_wrap_bcmp_TfibB
     rewrites that pc to PC_bcmp through TfibSyms' ts_code (lib/A/AF0l.v:15 pc_wrap_bcmp := 0x42668 = lib/A/FSH_Base.v
     PC_bcmp, sym __wrap_bcmp).
  - A10: lib/A/FSxSS.v:57 set_shadow_f5_contractU_x (a Theorem Labs lane, in S0 already).
  - A3 / A5 (fr_strlen / fr_memchr, H_strlen / H_memchr at S0 8fee0cc526f FSClose.v:162 / :166): lib/A/FSstrlen.v:835 fs_strlen_realizesU
    and lib/A/FSmemchr.v:268 fs_memchr_realizesU (a Theorem Labs lane, folded into S0 8fee0cc526f with its strfold
    0bc79e8d0f8), at PC_strlen / PC_memchr already; their FsRtCells premise is lib/A/FSrtcells.v fs_rt_cells_of, and
    FsShadowSyms TfibB (lib/A/FSH_Base.v:119, two GOT cells) holds by computation (fs_shadow_syms_TfibB below), so no
    TfibLib TfibB is needed here.
  - A8 / A9 (fr_memcpy / fr_memset, H_memcpy :172 / H_memset :174): lib/A/FSupoisonAsanC.v tfib_asan_memcpy_realizesU
    (a working branch 53ce9e4138c; with FSupoisonAsanR.v, both by path) and lib/A/FSxMset.v
    tfib_asan_memset_realizesU (a working branch d354a61f91e, blobs = fe33232c1fb's; with
    FSxMsetR.v, both by path), already at PC_memcpy 0x51d20 = __asan_memcpy / PC_memset 0x521bc = __asan_memset.
  AR_laws tfibsegs TfibB is lib/Reusable/YG0q.v:804 AR_laws_ok; TfibSyms TfibB is lib/A/AD2l.v:73 TfibB_syms.
  No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0l AF0m AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSH_YC20 FSH_Gen FSH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonU SetShadowDefU FSH_Rt.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSxSS FSupoisonCmp FSstrlen FSmemchr FSrtcells.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonAsanC FSxMset.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- a fact about TfibB, by computation ---- *)

(* the bcmp trampoline's pc in TfibB's code map is FSH_Base's PC_bcmp *)
Lemma pc_wrap_bcmp_TfibB : pc_wrap_bcmp (as_code TfibB) = PC_bcmp.
Proof. rewrite (ts_code _ TfibB_syms). reflexivity. Qed.

(* fs's two shadow GOT cells (lib/A/FSH_Base.v:119) in TfibB's symbol table, by computation *)
Lemma fs_shadow_syms_TfibB : FsShadowSyms TfibB.
Proof. unfold FsShadowSyms. split; vm_compute; reflexivity. Qed.

(* ---- the FsRt fields at segs := tfibsegs, B := TfibB ---- *)

(* A7: FsRt.fr_bcmp (lib/A/FSH_Rt.v:120) *)
Theorem rtA_bcmp : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FSupoisonU.abcmp_realizesU tfibsegs TfibB PC_bcmp.
Proof.
  intros rc fx. rewrite <- pc_wrap_bcmp_TfibB.
  apply FSupoisonCmp.tfib_abcmp_realizesU_closed; [apply AR_laws_ok | exact TfibB_syms].
Qed.

(* A3: FsRt.fr_strlen (lib/A/FSH_Rt.v:116) *)
Theorem rtA_strlen : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astrlen_realizesU tfibsegs TfibB PC_strlen.
Proof.
  intros rc fx.
  apply FSstrlen.fs_strlen_realizesU;
    [apply AR_laws_ok | exact TfibB_syms | exact fs_shadow_syms_TfibB
    | apply FSrtcells.fs_rt_cells_of; [apply AR_laws_ok | exact TfibB_syms]].
Qed.

(* A5: FsRt.fr_memchr (lib/A/FSH_Rt.v:118) *)
Theorem rtA_memchr : forall (rc : YM05.RunCeil) (fx : YK11.FPState), amemchr_realizesU tfibsegs TfibB PC_memchr.
Proof.
  intros rc fx.
  apply FSmemchr.fs_memchr_realizesU;
    [apply AR_laws_ok | exact TfibB_syms | exact fs_shadow_syms_TfibB
    | apply FSrtcells.fs_rt_cells_of; [apply AR_laws_ok | exact TfibB_syms]].
Qed.

(* A8: FsRt.fr_memcpy (lib/A/FSH_Rt.v:121) *)
Theorem rtA_memcpy : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  FSupoisonU.aintrin_realizesU tfibsegs TfibB OCpy PC_memcpy.
Proof.
  intros rc fx.
  apply FSupoisonAsanC.tfib_asan_memcpy_realizesU; [apply AR_laws_ok | exact TfibB_syms].
Qed.

(* A9: FsRt.fr_memset (lib/A/FSH_Rt.v:122) *)
Theorem rtA_memset : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  FSupoisonU.aintrin_realizesU tfibsegs TfibB OSet PC_memset.
Proof.
  intros rc fx.
  apply FSxMset.tfib_asan_memset_realizesU; [apply AR_laws_ok | exact TfibB_syms].
Qed.

(* A10: FsRt.fr_set_shadow_f5 (lib/A/FSH_Rt.v:123) *)
Theorem rtA_set_shadow_f5 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  SetShadowDefU.aset_shadow_realizesU tfibsegs TfibB PC_set_shadow_f5 0xf5.
Proof.
  intros rc fx.
  apply FSxSS.set_shadow_f5_contractU_x; [apply AR_laws_ok | exact TfibB_syms].
Qed.

(* Exactness check: each theorem above, at any rc and fx, IS its FsRt field at tfibsegs and TfibB (this definition
   type-checks only if so); the other fields are copied from a given record. *)
Definition rtA_fill (rc : YM05.RunCeil) (fx : YK11.FPState) (R : @FSH_Rt.FsRt fx rc tfibsegs TfibB) :
  @FSH_Rt.FsRt fx rc tfibsegs TfibB :=
  {| FSH_Rt.fr_strlen := rtA_strlen rc fx;
     FSH_Rt.fr_strcmp := @FSH_Rt.fr_strcmp fx rc tfibsegs TfibB R;
     FSH_Rt.fr_memchr := rtA_memchr rc fx;
     FSH_Rt.fr_snprintf := @FSH_Rt.fr_snprintf fx rc tfibsegs TfibB R;
     FSH_Rt.fr_bcmp := rtA_bcmp rc fx;
     FSH_Rt.fr_memcpy := rtA_memcpy rc fx;
     FSH_Rt.fr_memset := rtA_memset rc fx;
     FSH_Rt.fr_set_shadow_f5 := rtA_set_shadow_f5 rc fx;
     FSH_Rt.fr_malloc := @FSH_Rt.fr_malloc fx rc tfibsegs TfibB R;
     FSH_Rt.fr_free := @FSH_Rt.fr_free fx rc tfibsegs TfibB R;
     FSH_Rt.fr_stack_malloc_0 := @FSH_Rt.fr_stack_malloc_0 fx rc tfibsegs TfibB R;
     FSH_Rt.fr_stack_malloc_1 := @FSH_Rt.fr_stack_malloc_1 fx rc tfibsegs TfibB R;
     FSH_Rt.fr_stack_malloc_3 := @FSH_Rt.fr_stack_malloc_3 fx rc tfibsegs TfibB R |}.

About rtA_bcmp.
About rtA_set_shadow_f5.
About rtA_strlen.
About rtA_memchr.
About rtA_memcpy.
About rtA_memset.
Print Assumptions rtA_bcmp.
Print Assumptions rtA_set_shadow_f5.
Print Assumptions rtA_strlen.
Print Assumptions rtA_memchr.
Print Assumptions rtA_memcpy.
Print Assumptions rtA_memset.
