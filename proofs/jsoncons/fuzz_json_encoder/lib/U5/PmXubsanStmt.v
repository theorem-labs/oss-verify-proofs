(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The ubsan target half of ubsan_agrees, stated on its own: the ubsan image realizes the plain spec at
   target_alloc_limit for every input whose payload satisfies PHI. Shape of PmXasanFinalW.pm_xasan_tgt_stmtW with the
   ubsan image; the payload premise phi_okU is phrased with SpecG.hdr_okD, the form the source half produces
   (PmPhiX.phi_xsrc_at). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg SpinAlg Spec BigintSpec SpecG PmRef PmTopSpecsXW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmXubsanStmt.
(* The spurious-event configuration of the statement (Proof.v SpuriousCfgM.cfg, PmPhiX.cfg0). *)
Definition cfgU : SpuriousCfg := mkSpuriousCfg false true true true true true.

(* The payload predicate the source half yields at lim_source = 2^34. *)
Definition PHI0U : list byte -> Prop := PMXW.phi_lim (2 ^ 34).
Lemma PHI0U_IND : forall p, PHI0U p -> PMR.IND (map bv_unsigned p) < 2 ^ 34.
Proof. intros p H. exact H. Qed.

(* The harness payload of a file: the bytes after the 6-byte header and the CFG field (= Pm6DrvD.payload). *)
Definition payloadU (data : list byte) : list byte := skipn (Z.to_nat (6 + SpecG.cfgD data)) data.

(* PHI holds for the payload of the file named by argv[1], whenever the harness reaches its library call. *)
Definition phi_okU (PHI : list byte -> Prop) (path : list byte) (fs : Fs.Fs) : Prop :=
  (length path < 4096)%nat -> path <> [] -> path <> dot_path ->
  forall data, fs_lookup fs path = Some data -> SpecG.hdr_okD data -> PHI (payloadU data).

Abbreviation IMG_xubsan :=
  (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Definition pm_xubsan_tgt_stmt (scfg : SpuriousCfg) (PHI : list byte -> Prop) : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    in_va_size inp = Sv48 ->
    (forall a0s path, in_argv inp = [a0s; path] -> phi_okU PHI path (in_fs inp)) ->
    srealizes Ubsan.M.loaded_segments scfg
      (init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rdraw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
End FPX_1.
End PmXubsanStmt.
