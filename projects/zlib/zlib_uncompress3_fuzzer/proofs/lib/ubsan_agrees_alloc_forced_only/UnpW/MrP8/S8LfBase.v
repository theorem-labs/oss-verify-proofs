(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress3_fuzzer_repro.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec2 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec2Sound OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymRun OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDrive OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveX OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveH4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibKnowFrame OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8MainEntry OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8LibStdioCall OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8ExitBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8ReadBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8World.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition lf_ivs : list (Z * Z) :=
  [(0x10000, 0x21cb0); (0x21cb8, 0x22ee0); (0x22ee1, 0x22f29); (0x32f29, 0x72f60); (0x72f94, 0x72fe0); (0x72fe8, 0x73000);
   (0x73008, 0x73020); (0x73030, 0x73040); (0x73048, 0x93058); (0x93070, 0x93298); (0x932a0, 0x932a8); (0x936d8, 0x94000)]%Z.

(* [comment removed for export] *)
Definition knLF0 : list kentry :=
  [
     KAlign (EVar 0) 16;
     KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-6144513)) 6144513;
     KRange (EVar 2) 0x7fff80000000 0x800000400000;
     KWr (SA (ELit 0) 0x22000) 0x72000;
     KImg 0x10000 0x21cb0;
     KWord (SA (ELit 0) 0x21cb0) 8 (ELit 0x93298);
     KImg 0x21cb8 0x22ee0;
     KImg 0x22ee1 0x22f29;
     KImg 0x32f29 0x72f60;
     KImg 0x72f94 0x72fe0;
     KWord (SA (ELit 0) 0x72f88) 4 (EVar 5);
     KImg 0x72fe8 0x73000;
     KImg 0x73008 0x73020;
     KImg 0x73030 0x73040;
     KImg 0x73048 0x93058;
     KImg 0x93070 0x93298;
     KWord (SA (ELit 0) 0x93298) 8 (EVar 4);
     KImg 0x932a0 0x932a8;
     KWord (SA (ELit 0) 0x932bb) 1 (ELit 0);
     KImg 0x936d8 0x94000;
     KRange (EVar 5) 1 4194303]%Z.

(* [comment removed for export] *)
Definition ENVL (BL : list (list byte)) (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).
Definition valsLF (sp0 pp : word) (tid : Z) (R : bvmap 5 word) (cw : Z) : list word :=
  [sp0; pp; pp; pp; Z_to_bv 64 cw; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 0].

Section LfEntry.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
  Variable sp0 : word.
  Variable BL : list (list byte).
  Hypothesis Hvsp : valid_sp sp0.
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Variables (pp : word) (tid : Z) (R : bvmap 5 word) (M : word -> option byte) (cw : Z).
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) lf_ivs.
  Hypothesis Mtid : cell M 0x72f88 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mgot : cell M 0x21cb0 8 0x93298.
  Hypothesis Mcanary : cell M 0x93298 8 cw.
  Hypothesis Mnl : cell M 0x932bb 1 0.
  Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.
  Hypothesis Hpp2 : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z.

  Let E : env := ENVL BL (valsLF sp0 pp tid R cw).

  Lemma lf_img_clear_of : forall lo hi, In (lo, hi) lf_ivs -> img_clear M lo hi.
  Proof. intros lo hi Hin. exact (proj1 (Forall_forall _ _) Mimg (lo, hi) Hin). Qed.

  Ltac kimg := split; [lia|]; split; [lia|]; apply lf_img_clear_of; cbn; tauto.
  Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
                 rewrite adenot_lit0; cbn [edenot];
                 first [exact H | rewrite H; reflexivity | idtac].

  Lemma know_okLF : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M knLF0.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold know_ok, knLF0.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    - split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
    - change (edenot E (EVar 0)) with sp0. lia.
    - split; [apply flat_intro; cbn; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
      replace (bv_unsigned sp0 + -6144513 + d)%Z with (bv_unsigned sp0 - 6144513 + d)%Z by lia.
      apply Mstack; lia.
    - change (edenot E (EVar 2)) with pp. lia.
    - split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply store_ok_data; rewrite u_small by lia; lia.
    - kimg.
    - kcell Mgot.
    - kimg. - kimg. - kimg. - kimg.
    - kcell Mtid.
    - kimg. - kimg. - kimg. - kimg. - kimg.
    - kcell Mcanary.
    - kimg.
    - kcell Mnl.
    - kimg.
    - change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
  Qed.
End LfEntry.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
