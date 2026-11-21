(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 RefMemcpyLib LibKnowFrame. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S7MainEntry S7LibStdioCall S7ExitBase S7ReadBase S7World.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition lf_ivs : list (Z * Z) :=
  [(0x10000, 0x21c48); (0x21c50, 0x22e70); (0x22e71, 0x22eb9); (0x32eb9, 0x72ef0); (0x72f24, 0x72f70); (0x72f78, 0x72f90);
   (0x72f98, 0x72fb0); (0x72fc0, 0x72fd0); (0x72fd8, 0x92fe8); (0x93000, 0x93228); (0x93230, 0x93238); (0x93668, 0x94000)]%Z.

(* [comment removed for export] *)
Definition knLF0 : list kentry :=
  [
     KAlign (EVar 0) 16;
     KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-6144513)) 6144513;
     KRange (EVar 2) 0x7fff80000000 0x800000400000;
     KWr (SA (ELit 0) 0x22000) 0x72000;
     KImg 0x10000 0x21c48;
     KWord (SA (ELit 0) 0x21c48) 8 (ELit 0x93228);
     KImg 0x21c50 0x22e70;
     KImg 0x22e71 0x22eb9;
     KImg 0x32eb9 0x72ef0;
     KImg 0x72f24 0x72f70;
     KWord (SA (ELit 0) 0x72f18) 4 (EVar 5);
     KImg 0x72f78 0x72f90;
     KImg 0x72f98 0x72fb0;
     KImg 0x72fc0 0x72fd0;
     KImg 0x72fd8 0x92fe8;
     KImg 0x93000 0x93228;
     KWord (SA (ELit 0) 0x93228) 8 (EVar 4);
     KImg 0x93230 0x93238;
     KWord (SA (ELit 0) 0x9324b) 1 (ELit 0);
     KImg 0x93668 0x94000;
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
  Hypothesis Mtid : cell M 0x72f18 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mgot : cell M 0x21c48 8 0x93228.
  Hypothesis Mcanary : cell M 0x93228 8 cw.
  Hypothesis Mnl : cell M 0x9324b 1 0.
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
