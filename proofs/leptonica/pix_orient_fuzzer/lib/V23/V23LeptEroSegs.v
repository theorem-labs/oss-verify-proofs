(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRop GrayLib LeptRecs LeptSel LeptExec LeptExecW LeptExecB LeptExecX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23ExecUb V23LeptBase.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition SARE (m : word -> option byte) (s : Z) : word -> option byte :=
  wbytes m (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (Z_to_bv 64 0)).
Definition FRE (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)).
Definition PGE (m : word -> option byte) (s w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 w))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 h)).

Lemma er_ne_f : forall a b : Z, a = b -> branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof.
  intros a b ->. cbn [branch_taken]. unfold bv_eqb.
  first [ rewrite Z.eqb_refl; reflexivity | apply negb_false_iff; apply Z.eqb_eq; reflexivity ].
Qed.
Lemma er_eq_t : forall a b : Z, a = b -> branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
  intros a b ->. cbn [branch_taken]. unfold bv_eqb.
  first [ rewrite Z.eqb_refl; reflexivity | apply Z.eqb_eq; reflexivity ].
Qed.
Lemma er_seqz1 : forall p : Z, (1 <= p < 2 ^ 64)%Z -> alu64 ALU_SLTU (Z_to_bv 64 p) (Z_to_bv 64 1) = Z_to_bv 64 0.
Proof. intros p Hp. rewrite alu_sltu, WalksLib.v_sltu_Z by lia. rewrite (proj2 (Z.ltb_ge p 1)) by lia. reflexivity. Qed.

Ltac er_norm :=
  repeat first [ rewrite ex_sx32 by lia | rewrite w_subw | rewrite w_addw | rewrite m_mul | rewrite zbv_mul
               | rewrite ex_ptr_val | rewrite subw_fit by lia | rewrite addw_fit by lia | rewrite er_seqz1 by lia ].
Ltac er_sc_hook :=
  first [ v23_sc_hook
        | (er_norm; first [ (apply er_ne_f; lia) | (apply er_eq_t; lia) ]) ].
#[local] Ltac exB_sc_hook ::= er_sc_hook.
Ltac er_reg regs HR' :=
  lazymatch goal with
  | |- getr _ ?k = _ =>
      rewrite (reg_val _ _ _ k HR');
      match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
      ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
      repeat match goal with H : getr regs _ = _ |- _ => progress rewrite H end;
      er_norm;
      first [ reflexivity | assumption | (f_equal; lia) ]
  end.
Ltac er_at pc base rom fuel stops scr HR HK R' HR' Hms :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok ?segs _ _ ?kn =>
        let nx := ex_nx E in
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
            let Hsc := fresh "Hsc" in let Hlf := fresh "Hlf" in let Hex := fresh "Hex" in
            assert (Hex : sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr')) by (vm_cast_no_check (eq_refl (ss', scs, scr')));
            assert (Hsc : scs_denot segs base E scs);
            [ split_scs; lazymatch E with ex_envL _ ?r0 _ => ex_sc r0 end
            | destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc) as (R' & HR' & Hlf & Hms);
              clear Hsc Hlf Hex ]
        end
    end
  end.

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma er_A : forall regs m (s pixd pixs sel : Z) (ret : word),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
  getr regs 12 = Z_to_bv 64 sel ->
  exists regs',
    msteps SEGS (mkst regs (0xa1d7c : word) m rom) (mkst regs' (0xa1b7c : word) (FRE m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0xa1dc0 /\ getr regs' 9 = Z_to_bv 64 sel
    /\ getr regs' 18 = Z_to_bv 64 pixs /\ getr regs' 13 = Z_to_bv 64 (s - 144)
    /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 12 = Z_to_bv 64 sel
    /\ regs_agree (fun r => In r [1; 2; 9; 13; 18]%list) regs regs'.
Proof.
  intros regs m s pixd pixs sel ret Hs Hs64 SOK H2 H1 H10 H11 H12.
  replace (0xa1d7c : word) with (Z_to_bv 64 0xa1d7c) by (apply bv_eq; reflexivity).
  replace (0xa1b7c : word) with (Z_to_bv 64 0xa1b7c) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixd; pixs; sel] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd; pixs; sel]) m [KWr (SA (EVar 32) (-160)) 160]) by (ex_know regs).
  ex_run 400%nat [0xa1b7c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold FRE. subst ret. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma er_N : forall regs m (s : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (0xa1dc0 : word) m rom) (mkst regs' (0x63740 : word) m rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0xa2040 /\ getr regs' 10 = Z_to_bv 64 0x16ae9
    /\ getr regs' 11 = Z_to_bv 64 0x1deb2 /\ getr regs' 12 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RG RV H2 H10.
  replace (0xa1dc0 : word) with (Z_to_bv 64 0xa1dc0) by (apply bv_eq; reflexivity).
  replace (0x63740 : word) with (Z_to_bv 64 0x63740) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m
      [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3)]%Z) by (ex_know regs);
    ex_run 100%nat [0x63740%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.
Lemma er_Nz : forall regs m (s v : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : word),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= v < 2 ^ 64)%Z -> ret_ok ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v5) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v6) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v7) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v9) -> rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v10) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 v ->
  exists regs',
    msteps SEGS (mkst regs (0xa2040 : word) m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 v
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5
    /\ getr regs' 22 = v6 /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
Proof.
  intros regs m s v ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 Hs Hs64 Hv Hret R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H2 H10.
  replace (0xa2040 : word) with (Z_to_bv 64 0xa2040) by (apply bv_eq; reflexivity).
  ex_entryL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] regs [s; v] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] regs [s; v]) m
    [KWord (SA (EVar 44) (-8)) 8 (EVar 0); KWord (SA (EVar 44) (-16)) 8 (EVar 1); KWord (SA (EVar 44) (-24)) 8 (EVar 2);
     KWord (SA (EVar 44) (-32)) 8 (EVar 3); KWord (SA (EVar 44) (-40)) 8 (EVar 4); KWord (SA (EVar 44) (-48)) 8 (EVar 5);
     KWord (SA (EVar 44) (-56)) 8 (EVar 6); KWord (SA (EVar 44) (-64)) 8 (EVar 7); KWord (SA (EVar 44) (-72)) 8 (EVar 8);
     KWord (SA (EVar 44) (-80)) 8 (EVar 9); KWord (SA (EVar 44) (-88)) 8 (EVar 10); KWord (SA (EVar 44) (-96)) 8 (EVar 11);
     KRange (EVar 44) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs).
  ex_run 400%nat [0xa2084%Z] (SCR [] [] []) HR HK R' HR' Hms.
  assert (E1 : getr R' 1 = ret) by (ex_reg regs HR').
  exists R'. split.
  - cbn [s_pc] in Hms.
    assert (F : fetch_word SEGS (Z_to_bv 64 0xa2084) = Some (0x00008067 : bv 32)) by v23_vm_refl.
    assert (D : decode_any (0x00008067 : bv 32) = Some (Jalr 0 1 0, 4%Z)) by v23_vm_refl.
    eapply ex_msteps_snoc; [ex_mem regs Hms | reflexivity |].
    rewrite (step_jalr_x0 _ _ _ _ _ _ _ _ _ F eq_refl D E1).
    change (v_jalr ret (bv_signed (0 : bv 12))) with (v_jalr ret 0). rewrite (Hret : v_jalr ret 0 = ret). reflexivity.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma er_B : forall regs m (s pixd pixs sel w h : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs + 8 <= 2 ^ 64)%Z ->
  (pixs mod 8 = 0)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 w))) (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 104)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs -> getr regs 9 = Z_to_bv 64 sel ->
  exists regs',
    msteps SEGS (mkst regs (0xa1dc0 : word) m rom) (mkst regs' (0xa4fd0 : word) (PGE m s w h) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0xa1df4 /\ getr regs' 8 = Z_to_bv 64 pixd
    /\ getr regs' 10 = Z_to_bv 64 sel /\ getr regs' 11 = Z_to_bv 64 (s - 112) /\ getr regs' 12 = Z_to_bv 64 (s - 108)
    /\ getr regs' 13 = Z_to_bv 64 (s - 120) /\ getr regs' 14 = Z_to_bv 64 (s - 116)
    /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd pixs sel w h Hs Hs64 Hs16 Hd Hp1 Hp2 ALp Hw Hh RW RH SOK H2 H10 H18 H9.
  replace (0xa1dc0 : word) with (Z_to_bv 64 0xa1dc0) by (apply bv_eq; reflexivity).
  replace (0xa4fd0 : word) with (Z_to_bv 64 0xa4fd0) by (apply bv_eq; reflexivity).
  solve [
    assert (SOK1 : store_ok SEGS (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                     (Z_to_bv 64 (s - 104)) 8 = true) by (store_ok_peel; exact SOK);
    assert (SOK2 : store_ok SEGS (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                     (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 w))) (Z_to_bv 64 (s - 104)) 8 = true) by (store_ok_peel; exact SOK);
    ex_entry regs [s; pixd; pixs; sel; w; h] HR;
    assert (HK1 : know_ok SEGS (ex_env regs [s; pixd; pixs; sel; w; h]) m
      [KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 64 - 8);
       KAlign (EVar 32) 16; KAlign (EVar 34) 8; KWr (SA (EVar 32) (-104)) 8]%Z) by (ex_know regs);
    ex_run 200%nat [0x6e2e8%Z] (SCR [] [] []) HR HK1 R1 HR1 Hms1;
    cbn [s_pc s_regs s_log] in HR1, Hms1;
    assert (Hm1 : msteps SEGS (mkst regs (Z_to_bv 64 0xa1dc0) m rom)
      (mkst R1 (Z_to_bv 64 0x6e2e8) (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom))
      by (ex_mem regs Hms1);
    assert (HK2 : know_ok SEGS (ex_env regs [s; pixd; pixs; sel; w; h])
      (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      [KWord (SA (EVar 34) 0) 4 (EVar 36); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 32) 160 (2 ^ 64 - 1);
       KRange (EVar 34) 1 (2 ^ 64 - 8); KAlign (EVar 32) 16; KAlign (EVar 34) 8; KWr (SA (EVar 32) (-104)) 8]%Z) by (ex_know regs);
    er_at 0x6e2e8%Z (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      rom 100%nat [0x6e2fc%Z] (SCR [] [] []) HR1 HK2 R2 HR2 Hms2;
    cbn [s_pc s_regs s_log] in HR2, Hms2;
    assert (Hm2 : msteps SEGS
      (mkst R1 (Z_to_bv 64 0x6e2e8) (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      (mkst R2 (Z_to_bv 64 0x6e2fc) (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                                       (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 w))) rom))
      by (ex_mem2 regs Hms2);
    assert (HK3 : know_ok SEGS (ex_env regs [s; pixd; pixs; sel; w; h])
      (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
              (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
      [KWord (SA (EVar 34) 4) 4 (EVar 37); KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 32) 160 (2 ^ 64 - 1);
       KRange (EVar 34) 1 (2 ^ 64 - 8); KAlign (EVar 32) 16; KAlign (EVar 34) 8; KWr (SA (EVar 32) (-104)) 8]%Z) by (ex_know regs);
    er_at 0x6e2fc%Z (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                            (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
      rom 200%nat [0xa4fd0%Z] (SCR [] [] []) HR2 HK3 R3 HR3 Hms3;
    cbn [s_pc s_regs s_log] in HR3, Hms3;
    exists R3; split;
    [ eapply msteps_trans; [exact Hm1 |]; eapply msteps_trans; [exact Hm2 |]; unfold PGE; ex_mem2 regs Hms3
    | repeat split; try (er_reg regs HR3); ex_agree HR HR3 ] ].
Qed.

(* [comment removed for export] *)
Lemma er_C : forall regs m (pixd : Z),
  getr regs 8 = Z_to_bv 64 pixd ->
  exists regs',
    msteps SEGS (mkst regs (0xa1df4 : word) m rom) (mkst regs' (0x6ffb4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa1dfc /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m pixd H8.
  replace (0xa1df4 : word) with (Z_to_bv 64 0xa1df4) by (apply bv_eq; reflexivity).
  replace (0x6ffb4 : word) with (Z_to_bv 64 0x6ffb4) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [pixd] HR;
    assert (HK : know_ok SEGS (ex_env regs [pixd]) m []) by (ex_know regs);
    ex_run 20%nat [0x6ffb4%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_E : forall regs m (s sy sx sel : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z ->
  (0 <= sel < 2 ^ 64)%Z -> sel <> 0%Z -> (sel mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 sx) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 9 = Z_to_bv 64 sel ->
  exists regs',
    msteps SEGS (mkst regs (0xa1dfc : word) m rom) (mkst regs' (0xa1e94 : word) m rom)
    /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 1 /\ getr regs' 20 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 0x7fffffff
    /\ getr regs' 22 = Z_to_bv 64 (4 * 0) /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 24 = Z_to_bv 64 0
    /\ getr regs' 25 = Z_to_bv 64 (8 * 0) /\ getr regs' 26 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 sx
    /\ regs_agree (fun r => In r [10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
Proof.
  intros regs m s sy sx sel Hs Hs64 Hsy Hsx Hsel Hsel0 ALs RY RX H2 H9.
  replace (0xa1dfc : word) with (Z_to_bv 64 0xa1dfc) by (apply bv_eq; reflexivity).
  replace (0xa1e94 : word) with (Z_to_bv 64 0xa1e94) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; sy; sx; sel] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; sy; sx; sel]) m
      [KWord (SA (EVar 32) (-112)) 4 (EVar 33); KWord (SA (EVar 32) (-108)) 4 (EVar 34);
       KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1);
       KRange (EVar 35) 1 (2 ^ 64 - 1); KAlign (EVar 35) 8]%Z) by (ex_know regs);
    ex_run 200%nat [0xa1e94%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_L : forall regs m (s sy sx i j : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z -> (0 <= i < sy)%Z -> (0 <= j < sx)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 sx) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 sx ->
  getr regs 18 = Z_to_bv 64 i -> getr regs 20 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 0x7fffffff ->
  getr regs 22 = Z_to_bv 64 (4 * j) -> getr regs 23 = Z_to_bv 64 j -> getr regs 24 = Z_to_bv 64 j ->
  getr regs 25 = Z_to_bv 64 (8 * i) -> getr regs 26 = Z_to_bv 64 i ->
  exists regs' (pc : word),
    msteps SEGS (mkst regs (0xa1e84 : word) m rom) (mkst regs' pc m rom)
    /\ ( ((j + 1 < sx)%Z /\ pc = (0xa1e94 : word) /\ getr regs' 10 = Z_to_bv 64 sx /\ getr regs' 18 = Z_to_bv 64 i
          /\ getr regs' 22 = Z_to_bv 64 (4 * (j + 1)) /\ getr regs' 23 = Z_to_bv 64 (j + 1) /\ getr regs' 24 = Z_to_bv 64 (j + 1)
          /\ getr regs' 25 = Z_to_bv 64 (8 * i) /\ getr regs' 26 = Z_to_bv 64 i)
       \/ ((j + 1 = sx)%Z /\ (i + 1 < sy)%Z /\ pc = (0xa1e94 : word) /\ getr regs' 10 = Z_to_bv 64 sx /\ getr regs' 18 = Z_to_bv 64 (i + 1)
          /\ getr regs' 22 = Z_to_bv 64 (4 * 0) /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 24 = Z_to_bv 64 0
          /\ getr regs' 25 = Z_to_bv 64 (8 * (i + 1)) /\ getr regs' 26 = Z_to_bv 64 (i + 1))
       \/ ((j + 1 = sx)%Z /\ (i + 1 = sy)%Z /\ pc = (0xa1f10 : word)) )
    /\ regs_agree (fun r => In r [10; 18; 22; 23; 24; 25; 26]%list) regs regs'.
Proof.
  intros regs m s sy sx i j Hs Hs64 Hsy Hsx Hi Hj RY RX H2 H10 H18 H20 H21 H22 H23 H24 H25 H26.
  replace (0xa1e84 : word) with (Z_to_bv 64 0xa1e84) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; sy; sx; i; j; (4 * j)%Z; (8 * i)%Z] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; sy; sx; i; j; (4 * j)%Z; (8 * i)%Z]) m
      [KWord (SA (EVar 32) (-112)) 4 (EVar 33); KWord (SA (EVar 32) (-108)) 4 (EVar 34);
       KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1);
       KRange (EVar 35) 0 (2 ^ 31 - 2); KRange (EVar 36) 0 (2 ^ 31 - 2)]%Z) by (ex_know regs);
    destruct (Z.lt_ge_cases (j + 1) sx) as [Cj | Cj];
    [ ex_run 200%nat [0xa1e94%Z; 0xa1f10%Z] (SCR [false] [] []) HR HK R' HR' Hms;
      cbn [s_pc s_regs s_log] in Hms;
      exists R', (Z_to_bv 64 0xa1e94); split;
      [ exact Hms
      | split; [ left; repeat split; first [ lia | (apply bv_eq; reflexivity) | er_reg regs HR' ] | ex_agree HR HR' ] ]
    | destruct (Z.lt_ge_cases (i + 1) sy) as [Ci | Ci];
      [ ex_run 200%nat [0xa1e94%Z; 0xa1f10%Z] (SCR [true; false] [] []) HR HK R' HR' Hms;
        cbn [s_pc s_regs s_log] in Hms;
        exists R', (Z_to_bv 64 0xa1e94); split;
        [ exact Hms
        | split; [ right; left; repeat split; first [ lia | (apply bv_eq; reflexivity) | er_reg regs HR' ] | ex_agree HR HR' ] ]
      | ex_run 200%nat [0xa1e94%Z; 0xa1f10%Z] (SCR [true; true] [] []) HR HK R' HR' Hms;
        cbn [s_pc s_regs s_log] in Hms;
        exists R', (Z_to_bv 64 0xa1f10); split;
        [ exact Hms
        | split; [ right; right; repeat split; first [ lia | (apply bv_eq; reflexivity) ] | ex_agree HR HR' ] ] ] ] ].
Qed.

(* [comment removed for export] *)
Lemma er_M : forall regs m (sel data row i j c : Z),
  (0 <= sel)%Z -> (sel + 24 <= 2 ^ 64)%Z -> (0 <= data)%Z -> (data + 8 * i + 8 <= 2 ^ 64)%Z -> (0 <= row)%Z -> (row + 4 * j + 4 <= 2 ^ 64)%Z ->
  (0 <= i < 2 ^ 31)%Z -> (0 <= j < 2 ^ 31)%Z -> (0 <= c < 2 ^ 31)%Z -> c <> 1%Z ->
  data <> 0%Z -> (data mod 8 = 0)%Z -> row <> 0%Z -> (row mod 4 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
  rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
  rdn SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = Some (Z_to_le_bytes 4 c) ->
  getr regs 9 = Z_to_bv 64 sel -> getr regs 19 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 (4 * j) -> getr regs 25 = Z_to_bv 64 (8 * i) ->
  exists regs',
    msteps SEGS (mkst regs (0xa1e94 : word) m rom) (mkst regs' (0xa1e84 : word) m rom)
    /\ regs_agree (fun r => In r [11; 12; 13; 14]%list) regs regs'.
Proof.
  intros regs m sel data row i j c Hs1 Hs2 Hd1 Hd2 Hr1 Hr2 Hi Hj Hc Hc1 Hd0 ALd Hr0 ALr RD RR RC H9 H19 H22 H25.
  replace (0xa1e94 : word) with (Z_to_bv 64 0xa1e94) by (apply bv_eq; reflexivity).
  replace (0xa1e84 : word) with (Z_to_bv 64 0xa1e84) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [sel; data; row; i; j; c; (8 * i)%Z; (4 * j)%Z] HR;
    assert (HK : know_ok SEGS (ex_env regs [sel; data; row; i; j; c; (8 * i)%Z; (4 * j)%Z]) m
      [KWord (SA (EVar 32) 16) 8 (EVar 33); KWord (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 0) 8 (EVar 34);
       KWord (SA (EAlu ALU_ADD (EVar 34) (EVar 39)) 0) 4 (EVar 37);
       KRange (EVar 32) 0 (2 ^ 64 - 24); KRange (EVar 33) 1 (2 ^ 64 - 8); KRange (EVar 34) 1 (2 ^ 64 - 4);
       KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 34); KRange (EVar 39) 0 (2 ^ 33)]%Z)
      by (unfold know_ok;
          apply Forall_cons; [eapply ex_kword_Z; [ex_eden regs | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | exact RD] |];
          apply Forall_cons;
          [ eapply ex_kword_Z with (b := (data + 8 * i)%Z);
            [ ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
            | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RR ] |];
          apply Forall_cons;
          [ eapply ex_kword_Z with (b := (row + 4 * j)%Z);
            [ ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
            | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RC ] |];
          repeat (apply Forall_cons; [eapply ex_krange; [ex_eden regs | lia | lia] |]); apply Forall_nil);
    ex_run 400%nat [0xa1e84%Z] (SCR [false; false; false; false; false; false; true] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_H : forall regs m (s sel data row i j pixd pixt w h cx cy : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= sel)%Z -> (sel + 24 <= 2 ^ 64)%Z -> (0 <= data)%Z -> (data + 8 * i + 8 <= 2 ^ 64)%Z -> (0 <= row)%Z -> (row + 4 * j + 4 <= 2 ^ 64)%Z ->
  (0 <= i < 2 ^ 30)%Z -> (0 <= j < 2 ^ 30)%Z -> (0 <= cx < 2 ^ 30)%Z -> (0 <= cy < 2 ^ 30)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  (0 <= pixt < 2 ^ 64)%Z ->
  data <> 0%Z -> (data mod 8 = 0)%Z -> row <> 0%Z -> (row mod 4 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) ->
  rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
  rdn SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 cx) -> rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 cy) ->
  rdn SEGS m (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pixt) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 9 = Z_to_bv 64 sel -> getr regs 8 = Z_to_bv 64 pixd ->
  getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 (4 * j) -> getr regs 23 = Z_to_bv 64 j ->
  getr regs 25 = Z_to_bv 64 (8 * i) -> getr regs 26 = Z_to_bv 64 i ->
  exists regs',
    msteps SEGS (mkst regs (0xa1e94 : word) m rom) (mkst regs' (0x7f13c : word) (SARE m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa1e80 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 (cx - j)
    /\ getr regs' 12 = Z_to_bv 64 (cy - i) /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 h
    /\ getr regs' 15 = Z_to_bv 64 8 /\ getr regs' 16 = Z_to_bv 64 pixt /\ getr regs' 17 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s sel data row i j pixd pixt w h cx cy Hs Hs64 Hs1 Hs2 Hd1 Hd2 Hr1 Hr2 Hi Hj Hcx Hcy Hw Hh Hpt Hd0 ALd Hr0 ALr
    RD RR RC RCX RCY RW RH RPT SOK H2 H9 H8 H18 H19 H22 H23 H25 H26.
  replace (0xa1e94 : word) with (Z_to_bv 64 0xa1e94) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; sel; data; row; i; j; pixd; pixt; w; h; cx; cy; (8 * i)%Z; (4 * j)%Z] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; sel; data; row; i; j; pixd; pixt; w; h; cx; cy; (8 * i)%Z; (4 * j)%Z]) m
      [KWord (SA (EVar 33) 16) 8 (EVar 34); KWord (SA (EAlu ALU_ADD (EVar 34) (EVar 44)) 0) 8 (EVar 35);
       KWord (SA (EAlu ALU_ADD (EVar 35) (EVar 45)) 0) 4 (ELit 1);
       KWord (SA (EVar 32) (-116)) 4 (EVar 42); KWord (SA (EVar 32) (-120)) 4 (EVar 43);
       KWord (SA (EVar 32) (-100)) 4 (EVar 40); KWord (SA (EVar 32) (-104)) 4 (EVar 41);
       KWord (SA (EVar 32) (-144)) 8 (EVar 39); KWr (SA (EVar 32) (-160)) 8;
       KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 24); KRange (EVar 34) 1 (2 ^ 64 - 8); KRange (EVar 35) 1 (2 ^ 64 - 4);
       KRange (EVar 36) 0 (2 ^ 30 - 1); KRange (EVar 37) 0 (2 ^ 30 - 1); KRange (EVar 40) 0 (2 ^ 31 - 1); KRange (EVar 41) 0 (2 ^ 31 - 1);
       KRange (EVar 42) 0 (2 ^ 30 - 1); KRange (EVar 43) 0 (2 ^ 30 - 1); KRange (EVar 44) 0 (2 ^ 34); KRange (EVar 45) 0 (2 ^ 33)]%Z)
      by (unfold know_ok;
          apply Forall_cons; [eapply ex_kword_Z; [ex_eden regs | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | exact RD] |];
          apply Forall_cons;
          [ eapply ex_kword_Z with (b := (data + 8 * i)%Z);
            [ ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
            | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RR ] |];
          apply Forall_cons;
          [ eapply ex_kword_Z with (b := (row + 4 * j)%Z);
            [ ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; apply ex_ptr_val
            | ex_eden regs | lia | lia | lia | lia | cbn; lia | lia | rewrite Z.add_0_r; exact RC ] |];
          repeat (apply Forall_cons; [ex_know1 regs |]); apply Forall_nil);
    ex_run 400%nat [0x7f13c%Z] (SCR [false; false; false; false; false; false; false; true] [] []) HR HK R' HR' Hms;
    exists R'; split; [ unfold SARE; ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_R : forall regs m (s sx : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sx < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 sx) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs',
    msteps SEGS (mkst regs (0xa1e80 : word) m rom) (mkst regs' (0xa1e84 : word) m rom)
    /\ getr regs' 10 = Z_to_bv 64 sx /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof.
  intros regs m s sx Hs Hs64 Hsx RX H2.
  replace (0xa1e80 : word) with (Z_to_bv 64 0xa1e80) by (apply bv_eq; reflexivity).
  replace (0xa1e84 : word) with (Z_to_bv 64 0xa1e84) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; sx] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; sx]) m
      [KWord (SA (EVar 32) (-108)) 4 (EVar 33); KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1)]%Z) by (ex_know regs);
    ex_run 20%nat [0xa1e84%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_T : forall regs m (s sel : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> rdn SEGS m (Z_to_bv 64 0x127ca0) 4 = Some (Z_to_le_bytes 4 1) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 9 = Z_to_bv 64 sel ->
  exists regs',
    msteps SEGS (mkst regs (0xa1f10 : word) m rom) (mkst regs' (0xa5590 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa1f38 /\ getr regs' 10 = Z_to_bv 64 sel /\ getr regs' 11 = Z_to_bv 64 (s - 124)
    /\ getr regs' 12 = Z_to_bv 64 (s - 128) /\ getr regs' 13 = Z_to_bv 64 (s - 132) /\ getr regs' 14 = Z_to_bv 64 (s - 136)
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros regs m s sel Hs Hs64 RM H2 H9.
  replace (0xa1f10 : word) with (Z_to_bv 64 0xa1f10) by (apply bv_eq; reflexivity).
  replace (0xa5590 : word) with (Z_to_bv 64 0xa5590) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; sel] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; sel]) m [KWord (SA (ELit 0) 0x127ca0) 4 (ELit 1)]%Z) by (ex_know regs);
    ex_run 50%nat [0xa5590%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_X1s : forall regs m (s : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 0) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs', msteps SEGS (mkst regs (0xa1f38 : word) m rom) (mkst regs' (0xa1f64 : word) m rom) /\ regs_agree (fun r => In r [13]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RX H2.
  replace (0xa1f38 : word) with (Z_to_bv 64 0xa1f38) by (apply bv_eq; reflexivity).
  replace (0xa1f64 : word) with (Z_to_bv 64 0xa1f64) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWord (SA (EVar 32) (-124)) 4 (ELit 0); KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs);
    ex_run 20%nat [0xa1f64%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | ex_agree HR HR' ] ].
Qed.
Lemma er_X1c : forall regs m (s pixd xp h : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= xp < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 xp) -> rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true -> getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs', msteps SEGS (mkst regs (0xa1f38 : word) m rom) (mkst regs' (0x7f13c : word) (SARE m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa1f64 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 xp /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd xp h Hs Hs64 Hx Hh RX RH SOK H2 H8.
  replace (0xa1f38 : word) with (Z_to_bv 64 0xa1f38) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; pixd; xp; h] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; xp; h]) m
      [KWord (SA (EVar 32) (-124)) 4 (EVar 34); KWord (SA (EVar 32) (-104)) 4 (EVar 35); KWr (SA (EVar 32) (-160)) 8;
       KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs);
    ex_run 50%nat [0x7f13c%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ unfold SARE; ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_X2s : forall regs m (s : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 0) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs', msteps SEGS (mkst regs (0xa1f64 : word) m rom) (mkst regs' (0xa1fa0 : word) m rom) /\ regs_agree (fun r => In r [13]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RX H2.
  replace (0xa1f64 : word) with (Z_to_bv 64 0xa1f64) by (apply bv_eq; reflexivity).
  replace (0xa1fa0 : word) with (Z_to_bv 64 0xa1fa0) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWord (SA (EVar 32) (-132)) 4 (ELit 0); KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs);
    ex_run 20%nat [0xa1fa0%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | ex_agree HR HR' ] ].
Qed.
Lemma er_X2c : forall regs m (s pixd xn w h : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= xn < 2 ^ 30)%Z -> (0 <= w < 2 ^ 30)%Z -> (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 xn) -> rdn SEGS m (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true -> getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs', msteps SEGS (mkst regs (0xa1f64 : word) m rom) (mkst regs' (0x7f13c : word) (SARE m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa1fa0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 (w - xn) /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 xn /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd xn w h Hs Hs64 Hx Hw Hh RX RW RH SOK H2 H8.
  replace (0xa1f64 : word) with (Z_to_bv 64 0xa1f64) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; pixd; xn; w; h] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; xn; w; h]) m
      [KWord (SA (EVar 32) (-132)) 4 (EVar 34); KWord (SA (EVar 32) (-100)) 4 (EVar 35); KWord (SA (EVar 32) (-104)) 4 (EVar 36);
       KWr (SA (EVar 32) (-160)) 8; KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 30 - 1);
       KRange (EVar 35) 0 (2 ^ 30 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs);
    ex_run 50%nat [0x7f13c%Z] (SCR [false] [] []) HR HK R' HR' Hms;
    exists R'; split; [ unfold SARE; ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_X3s : forall regs m (s : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 0) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs', msteps SEGS (mkst regs (0xa1fa0 : word) m rom) (mkst regs' (0xa1fcc : word) m rom) /\ regs_agree (fun r => In r [14]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RX H2.
  replace (0xa1fa0 : word) with (Z_to_bv 64 0xa1fa0) by (apply bv_eq; reflexivity).
  replace (0xa1fcc : word) with (Z_to_bv 64 0xa1fcc) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWord (SA (EVar 32) (-128)) 4 (ELit 0); KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs);
    ex_run 20%nat [0xa1fcc%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | ex_agree HR HR' ] ].
Qed.
Lemma er_X3c : forall regs m (s pixd yp w : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= yp < 2 ^ 31)%Z -> (0 <= w < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 yp) -> rdn SEGS m (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 w) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true -> getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs', msteps SEGS (mkst regs (0xa1fa0 : word) m rom) (mkst regs' (0x7f13c : word) (SARE m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa1fcc /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 yp /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd yp w Hs Hs64 Hy Hw RY RW SOK H2 H8.
  replace (0xa1fa0 : word) with (Z_to_bv 64 0xa1fa0) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; pixd; yp; w] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; yp; w]) m
      [KWord (SA (EVar 32) (-128)) 4 (EVar 34); KWord (SA (EVar 32) (-100)) 4 (EVar 35); KWr (SA (EVar 32) (-160)) 8;
       KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 31 - 1); KRange (EVar 35) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs);
    ex_run 50%nat [0x7f13c%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ unfold SARE; ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_X4s : forall regs m (s : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 0) -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs', msteps SEGS (mkst regs (0xa1fcc : word) m rom) (mkst regs' (0xa2008 : word) m rom) /\ regs_agree (fun r => In r [14]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 RX H2.
  replace (0xa1fcc : word) with (Z_to_bv 64 0xa1fcc) by (apply bv_eq; reflexivity).
  replace (0xa2008 : word) with (Z_to_bv 64 0xa2008) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWord (SA (EVar 32) (-136)) 4 (ELit 0); KRange (EVar 32) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs);
    ex_run 20%nat [0xa2008%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | ex_agree HR HR' ] ].
Qed.
Lemma er_X4c : forall regs m (s pixd yn w h : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= yn < 2 ^ 30)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 30)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 yn) -> rdn SEGS m (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 160)) 8 = true -> getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs', msteps SEGS (mkst regs (0xa1fcc : word) m rom) (mkst regs' (0x7f13c : word) (SARE m s) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa2008 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (h - yn)
    /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 yn /\ getr regs' 15 = Z_to_bv 64 0 /\ getr regs' 16 = Z_to_bv 64 0
    /\ getr regs' 17 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros regs m s pixd yn w h Hs Hs64 Hy Hw Hh RY RW RH SOK H2 H8.
  replace (0xa1fcc : word) with (Z_to_bv 64 0xa1fcc) by (apply bv_eq; reflexivity).
  replace (0x7f13c : word) with (Z_to_bv 64 0x7f13c) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s; pixd; yn; w; h] HR;
    assert (HK : know_ok SEGS (ex_env regs [s; pixd; yn; w; h]) m
      [KWord (SA (EVar 32) (-136)) 4 (EVar 34); KWord (SA (EVar 32) (-100)) 4 (EVar 35); KWord (SA (EVar 32) (-104)) 4 (EVar 36);
       KWr (SA (EVar 32) (-160)) 8; KRange (EVar 32) 160 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 30 - 1);
       KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 30 - 1)]%Z) by (ex_know regs);
    ex_run 50%nat [0x7f13c%Z] (SCR [false] [] []) HR HK R' HR' Hms;
    exists R'; split; [ unfold SARE; ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_F : forall regs m (s : Z),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 160) ->
  exists regs',
    msteps SEGS (mkst regs (0xa2008 : word) m rom) (mkst regs' (0x6df98 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa2010 /\ getr regs' 10 = Z_to_bv 64 (s - 144)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros regs m s Hs Hs64 H2.
  replace (0xa2008 : word) with (Z_to_bv 64 0xa2008) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  solve [
    ex_entry regs [s] HR;
    assert (HK : know_ok SEGS (ex_env regs [s]) m []) by (ex_know regs);
    ex_run 20%nat [0x6df98%Z] (SCR [] [] []) HR HK R' HR' Hms;
    exists R'; split; [ ex_mem regs Hms | repeat split; try (er_reg regs HR'); ex_agree HR HR' ] ].
Qed.

(* [comment removed for export] *)
Lemma er_Z : forall regs m (s pixd : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : word),
  (160 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v5) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v6) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v7) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v9) -> rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v10) ->
  getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs',
    msteps SEGS (mkst regs (0xa2010 : word) m rom) (mkst regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 pixd
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5
    /\ getr regs' 22 = v6 /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
Proof.
  intros regs m s pixd ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 Hs Hs64 Hret R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 H2 H8.
  replace (0xa2010 : word) with (Z_to_bv 64 0xa2010) by (apply bv_eq; reflexivity).
  ex_entryL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] regs [s; pixd] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10] regs [s; pixd]) m
    [KWord (SA (EVar 44) (-8)) 8 (EVar 0); KWord (SA (EVar 44) (-16)) 8 (EVar 1); KWord (SA (EVar 44) (-24)) 8 (EVar 2);
     KWord (SA (EVar 44) (-32)) 8 (EVar 3); KWord (SA (EVar 44) (-40)) 8 (EVar 4); KWord (SA (EVar 44) (-48)) 8 (EVar 5);
     KWord (SA (EVar 44) (-56)) 8 (EVar 6); KWord (SA (EVar 44) (-64)) 8 (EVar 7); KWord (SA (EVar 44) (-72)) 8 (EVar 8);
     KWord (SA (EVar 44) (-80)) 8 (EVar 9); KWord (SA (EVar 44) (-88)) 8 (EVar 10); KWord (SA (EVar 44) (-96)) 8 (EVar 11);
     KRange (EVar 44) 160 (2 ^ 64 - 1)]%Z) by (ex_know regs).
  ex_run 400%nat [0xa2084%Z] (SCR [] [] []) HR HK R' HR' Hms.
  assert (E1 : getr R' 1 = ret) by (ex_reg regs HR').
  exists R'. split.
  - cbn [s_pc] in Hms.
    assert (F : fetch_word SEGS (Z_to_bv 64 0xa2084) = Some (0x00008067 : bv 32)) by v23_vm_refl.
    assert (D : decode_any (0x00008067 : bv 32) = Some (Jalr 0 1 0, 4%Z)) by v23_vm_refl.
    eapply ex_msteps_snoc; [ex_mem regs Hms | reflexivity |].
    rewrite (step_jalr_x0 _ _ _ _ _ _ _ _ _ F eq_refl D E1).
    change (v_jalr ret (bv_signed (0 : bv 12))) with (v_jalr ret 0). rewrite (Hret : v_jalr ret 0 = ret). reflexivity.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

End Segs.
