(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 RefMemcpyLib LibKnowFrame
  S0MainEntry S0LibStdioCall S0ExitBase S0ReadBase S0World.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition lf_ivs : list (Z * Z) :=
  [(0x10000,0x1e780); (0x1e788,0x1f9b0); (0x1f9b1,0x1f9f9); (0x2f9f9,0x2fa30); (0x2fa64,0x2fab0); (0x2fab8,0x2fad0);
   (0x2fad8,0x2faf0); (0x2fb00,0x2fb10); (0x2fb18,0x4fb28); (0x4fb40,0x4fd70); (0x4fd78,0x4fd80); (0x501b0,0x51000)]%Z.

Definition knLF0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-6144513)) 6144513;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0x1f000) 0x32000;
   KImg 0x10000 0x1e780;
   KWord (SA (ELit 0) 0x1e780) 8 (ELit 0x4fd70);
   KImg 0x1e788 0x1f9b0; KImg 0x1f9b1 0x1f9f9; KImg 0x2f9f9 0x2fa30; KImg 0x2fa64 0x2fab0;
   KWord (SA (ELit 0) 0x2fa58) 4 (EVar 5);
   KImg 0x2fab8 0x2fad0; KImg 0x2fad8 0x2faf0; KImg 0x2fb00 0x2fb10;
   KImg 0x2fb18 0x4fb28; KImg 0x4fb40 0x4fd70;
   KWord (SA (ELit 0) 0x4fd70) 8 (EVar 4);
   KImg 0x4fd78 0x4fd80;
   KWord (SA (ELit 0) 0x4fd93) 1 (ELit 0);
   KImg 0x501b0 0x51000;
   KRange (EVar 5) 1 4194303]%Z.

Definition ENVL (BL : list (list byte)) (vals : list word) : env := Env (vals_ev vals) (blobs_ev BL).
Definition valsLF (sp0 pp : word) (tid : Z) (R : bvmap 5 word) (cw : Z) : list word :=
  [sp0; pp; pp; pp; Z_to_bv 64 cw; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 0].

Section LfEntry.
Context {RCa1 : RunCtx}.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Hypothesis Hvsp : valid_sp sp0.
  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Variables (pp : word) (tid : Z) (R : bvmap 5 word) (M : word -> option byte) (cw : Z).
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) lf_ivs.
  Hypothesis Mtid : cell M 0x2fa58 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mgot : cell M 0x1e780 8 0x4fd70.
  Hypothesis Mcanary : cell M 0x4fd70 8 cw.
  Hypothesis Mnl : cell M 0x4fd93 1 0.
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
