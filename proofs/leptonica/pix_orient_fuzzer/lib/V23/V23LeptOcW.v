(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptSlots.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL LeptCmapArr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecW LeptExecFP LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyTR O23LeptPixCopyT O23LeptSelGP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LiaRel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptOcSegs O23LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptOcW O23LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptMbc V23LeptOc_iface V23LeptUdd_iface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23ExecUb V23LeptErr V23LeptStderrP8 V23LeptMod V23LeptRot90W V23LeptRot180W V23LeptRotOrthW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptPixCopyT V23LeptPixDestroyK V23LeptPixMisc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_frontB_oce.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_rel.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_rel.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Ltac exB_sc_hook ::= v23_sc_hook.

(* [comment removed for export] *)
Definition OC_STACK (udd_stk : Z) : Z := 96 + Z.max udd_stk 3680.
Definition RK_oc (rk_udd : Z) : Z := 2 * rk_udd + (RK_pix + RK_cmapcopy) + (RK_pixcopy + 3).
Definition RB_oc_arm (w h cm : Z) : Z :=
  Z.max (RB_pixT (4 * (wpl_of h 1 * w)) + RB_cmapcopy)
        (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm + alloc_margin 256 + 2 * alloc_margin (4 * wpl_of w 1)).
Definition RB_oc (rb_udd : Z -> Z -> Z -> Z) (w h cm : Z) : Z :=
  rb_udd w h cm + (RB_pixT (4 * (wpl_of h 1 * w)) + RB_cmapcopy) + rb_udd h w 1%Z + RB_oc_arm w h cm.

Local Ltac xopq t z EQ :=
  pose (z := bv_unsigned t);
  assert (EQ : t = Z_to_bv 64 z) by (unfold z; symmetry; apply zbv_self);
  clearbody z.

Local Ltac xfstep fdef HK ST FZ :=
  lazymatch type of ST with
  | ex_st ?segs ?E ?m ?rom ?ms0 (mkFP (fr_denot _ ?L ?fr) ?cs) ?pc ?sr ?log =>
    let F := fresh "F" in let D := fresh "D" in
    ex_fetch segs pc F D;
    lazymatch type of D with
    | decode_any ?w = Some (Fsgnj ?op ?fmt ?rd ?rs1 ?rs2, _) =>
        let z := fresh "zs" in let EQ := fresh "EQs" in let ST' := fresh "ST" in
        xopq (fpv_sgnj op fmt (reg_get (fr_denot E L fr) rs1) (reg_get (fr_denot E L fr) rs2)) z EQ;
        pose proof (exb_fsgnj segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 _ _ z ST F (eq_refl _) D eq_refl eq_refl EQ) as ST';
        clear F D EQ ST; rename ST' into ST; exb_norm ST
    | decode_any ?w = Some (FLoad FMT_S ?rd ?rs ?imm, _) =>
        lazymatch type of HK with
        | know_ok _ _ _ ?kn =>
          let r0 := lazymatch E with ex_envL _ ?r0 _ => r0 end in
          let a := eval vm_compute in (to_saddrK kn (sr_get sr rs) (bv_signed imm)) in
          lazymatch a with
          | SA ?rb ?rk =>
            let lk := eval vm_compute in (ex_lookup segs kn log rb rk 4) in
            lazymatch lk with
            | Some (?v, ?scs) =>
              let scs0 := eval vm_compute in (flat_sc kn a 4 ++ scs) in
              let z := fresh "zf" in let EQ := fresh "EQf" in let ST' := fresh "ST" in
              xopq (nan_box (bv_extract 0 32 (edenot E v))) z EQ;
              pose proof (exb_flw segs E L fr cs m rom pc sr log kn ms0 w rd rs imm v scs z ST HK F (eq_refl _) D rb rk scs0
                            ltac:(vm_cast_no_check (eq_refl a)) ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0))
                            ltac:(exb_scs r0) EQ) as ST';
              clear F D EQ ST; rename ST' into ST; exb_norm ST
            end
          end
        end
    | _ => clear F D; exb_fstep fdef HK ST FZ; exb_norm ST
    end
  end.

Local Ltac xrun fdef stops scr HK ST FZ :=
  exb_cont 300%nat stops scr HK ST ltac:(fun scr' =>
    first [ exb_at_stop stops ST
          | (xfstep fdef HK ST FZ; first [ exb_at_stop stops ST | xrun fdef stops scr' HK ST FZ ]) ]).

Local Ltac xval regs :=
  ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = _ |- _ => progress rewrite H end;
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | |- ?x = Z_to_bv 64 (bv_unsigned ?x) => symmetry; apply zbv_self
  | |- Z_to_bv 64 (bv_unsigned ?x) = ?x => apply zbv_self
  | _ => first [ (f_equal; lia) | ex_val regs ]
  end.

Local Ltac xmem regs :=
  cbn [mem_denot s_log e_addr e_width e_val];
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | f_equal; xval regs ]);
  reflexivity.

Local Ltac xreg regs HR' := v23_reg regs HR'.

Definition OC_FDEF : list (nat * nat) := [(8%nat, 39%nat); (9%nat, 40%nat)].

Section Segs.
Variable rom : word -> option byte.

Lemma oc_P : forall fr cs regs m (s pixs pup plf prot dbg d : Z) (ret : word),
  frm_zero cs ->
  (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs + 64 <= 2 ^ 64)%Z -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z -> (0 <= d < 2 ^ 31)%Z ->
  (pixs mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 pup ->
  getr regs 12 = Z_to_bv 64 plf -> getr regs 13 = Z_to_bv 64 prot -> getr regs 14 = Z_to_bv 64 dbg ->
  exists fr' regs',
    msteps SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0xaf5d8) m rom)
                (@mkst (mkFP fr' cs) regs' (Z_to_bv 64 0xaf620) (O23LeptOcSegs.OCF m s ret regs fr) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 8 = Z_to_bv 64 pixs
    /\ getr regs' 9 = Z_to_bv 64 prot /\ getr regs' 18 = Z_to_bv 64 dbg /\ getr regs' 19 = Z_to_bv 64 plf /\ getr regs' 20 = Z_to_bv 64 pup
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20]%list) regs regs'.
Proof.
  intros fr cs regs m s pixs pup plf prot dbg d ret FZ Hs1 Hs2 Hp1 Hp2 Hps Hd ALp RD SOK R2 R1 R10 R11 R12 R13 R14.
  pose proof (u64_range (reg_get fr 8%bv)) as F8. pose proof (u64_range (reg_get fr 9%bv)) as F9.
  ex_entry regs [s; pixs; pup; plf; prot; dbg; d; bv_unsigned (reg_get fr 8%bv); bv_unsigned (reg_get fr 9%bv)] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; pup; plf; prot; dbg; d; bv_unsigned (reg_get fr 8%bv); bv_unsigned (reg_get fr 9%bv)]) m
                 [KWr (SA (EVar 32) (-96)) 96; KRange (EVar 33) 1 (2 ^ 64 - 64); KAlign (EVar 33) 8; KWord (SA (EVar 33) 8) 4 (EVar 38);
                  KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-96)) 96]%Z) by ex_know regs.
  exb_open HR HK ST.
  xrun OC_FDEF [0xaf620]%Z (SCR [] [] []) HK ST FZ.
  exb_exit ST R HRx Hlf Hms.
  eexists _, R. split.
  { eapply ex_msteps_mem; [exact Hms |]. unfold O23LeptOcSegs.OCF. xmem regs. }
  idtac "TIME P-regs".
  repeat split; try (xreg regs HRx). ex_agree HR HRx.
Time Qed.

(* [comment removed for export] *)
Lemma oc_K4b : forall (fx : FPState) regs m (prot pixs : Z),
  (1 <= prot)%Z -> (prot + 4 <= 2 ^ 64)%Z -> (prot mod 4 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 prot) 4 = true ->
  getr regs 9 = Z_to_bv 64 prot -> getr regs 8 = Z_to_bv 64 pixs ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf788 : word) m rom) (@mkst fx regs' (0x97094 : word) (wr4 m prot 270) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf818 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 3
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m prot pixs Hp1 Hp2 ALp SOK R9 R8.
  replace (0xaf788 : word) with (Z_to_bv 64 0xaf788) by (apply bv_eq; reflexivity).
  replace (0x97094 : word) with (Z_to_bv 64 0x97094) by (apply bv_eq; reflexivity).
  ex_entry regs [prot; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [prot; pixs]) m [KWr (SA (EVar 32) 0) 4; KRange (EVar 32) 1 (2 ^ 64 - 4); KAlign (EVar 32) 4]) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x97094%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [| split; [| split; [| split]]].
  - unfold wr4. ex_mem regs Hms.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_agree HRo HR.
Qed.

Lemma oc_K0b : forall (fx : FPState) regs m (prot pixs : Z),
  (1 <= prot)%Z -> (prot + 4 <= 2 ^ 64)%Z -> (prot mod 4 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 prot) 4 = true ->
  getr regs 9 = Z_to_bv 64 prot -> getr regs 8 = Z_to_bv 64 pixs ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf75c : word) m rom) (@mkst fx regs' (0x6eb5c : word) (wr4 m prot 0) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf874 /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixs
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m prot pixs Hp1 Hp2 ALp SOK R9 R8.
  replace (0xaf75c : word) with (Z_to_bv 64 0xaf75c) by (apply bv_eq; reflexivity).
  replace (0x6eb5c : word) with (Z_to_bv 64 0x6eb5c) by (apply bv_eq; reflexivity).
  ex_entry regs [prot; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [prot; pixs]) m [KWr (SA (EVar 32) 0) 4; KRange (EVar 32) 1 (2 ^ 64 - 4); KAlign (EVar 32) 4]) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x6eb5c%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [| split; [| split; [| split]]].
  - unfold wr4. ex_mem regs Hms.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_agree HRo HR.
Qed.

(* [comment removed for export] *)
Lemma oc_K01b : forall (fx : FPState) regs m (prot pixs : Z),
  (1 <= prot)%Z -> (prot + 4 <= 2 ^ 64)%Z -> (prot mod 4 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 prot) 4 = true ->
  getr regs 9 = Z_to_bv 64 prot -> getr regs 8 = Z_to_bv 64 pixs ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf838 : word) m rom) (@mkst fx regs' (0x6eb5c : word) (wr4 m prot 0) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf874 /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixs
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m prot pixs Hp1 Hp2 ALp SOK R9 R8.
  replace (0xaf838 : word) with (Z_to_bv 64 0xaf838) by (apply bv_eq; reflexivity).
  replace (0x6eb5c : word) with (Z_to_bv 64 0x6eb5c) by (apply bv_eq; reflexivity).
  ex_entry regs [prot; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [prot; pixs]) m [KWr (SA (EVar 32) 0) 4; KRange (EVar 32) 1 (2 ^ 64 - 4); KAlign (EVar 32) 4]) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x6eb5c%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [| split; [| split; [| split]]].
  - unfold wr4. ex_mem regs Hms.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_agree HRo HR.
Qed.

(* [comment removed for export] *)
Lemma oc_K2b : forall (fx : FPState) regs m (prot pixs : Z),
  (1 <= prot)%Z -> (prot + 4 <= 2 ^ 64)%Z -> (prot mod 4 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 prot) 4 = true ->
  getr regs 9 = Z_to_bv 64 prot -> getr regs 8 = Z_to_bv 64 pixs ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf7c0 : word) m rom) (@mkst fx regs' (0x97094 : word) (wr4 m prot 90) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf818 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m prot pixs Hp1 Hp2 ALp SOK R9 R8.
  replace (0xaf7c0 : word) with (Z_to_bv 64 0xaf7c0) by (apply bv_eq; reflexivity).
  replace (0x97094 : word) with (Z_to_bv 64 0x97094) by (apply bv_eq; reflexivity).
  ex_entry regs [prot; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [prot; pixs]) m [KWr (SA (EVar 32) 0) 4; KRange (EVar 32) 1 (2 ^ 64 - 4); KAlign (EVar 32) 4]) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x97094%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [| split; [| split; [| split]]].
  - unfold wr4. ex_mem regs Hms.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_agree HRo HR.
Qed.

(* [comment removed for export] *)
Lemma oc_K3b : forall (fx : FPState) regs m (prot pixs : Z),
  (1 <= prot)%Z -> (prot + 4 <= 2 ^ 64)%Z -> (prot mod 4 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 prot) 4 = true ->
  getr regs 9 = Z_to_bv 64 prot -> getr regs 8 = Z_to_bv 64 pixs ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf7f8 : word) m rom) (@mkst fx regs' (0x97094 : word) (wr4 m prot 180) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf818 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 2
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m prot pixs Hp1 Hp2 ALp SOK R9 R8.
  replace (0xaf7f8 : word) with (Z_to_bv 64 0xaf7f8) by (apply bv_eq; reflexivity).
  replace (0x97094 : word) with (Z_to_bv 64 0x97094) by (apply bv_eq; reflexivity).
  ex_entry regs [prot; pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [prot; pixs]) m [KWr (SA (EVar 32) 0) 4; KRange (EVar 32) 1 (2 ^ 64 - 4); KAlign (EVar 32) 4]) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x97094%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [| split; [| split; [| split]]].
  - unfold wr4. ex_mem regs Hms.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_reg regs HR.
  - ex_agree HRo HR.
Qed.

(* [comment removed for export] *)
Lemma oc_K0a : forall (fx : FPState) regs m, getr regs 10 = Z_to_bv 64 3 ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf740 : word) m rom) (@mkst fx regs' (0x636a4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf75c /\ getr regs' 10 = Z_to_bv 64 0x113ab /\ getr regs' 11 = Z_to_bv 64 0x1055c
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m R10.
  replace (0xaf740 : word) with (Z_to_bv 64 0xaf740) by (apply bv_eq; reflexivity).
  replace (0x636a4 : word) with (Z_to_bv 64 0x636a4) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x636a4%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
Qed.

Lemma oc_K1a : forall (fx : FPState) regs m, getr regs 10 = Z_to_bv 64 3 ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf81c : word) m rom) (@mkst fx regs' (0x636a4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf838 /\ getr regs' 10 = Z_to_bv 64 0x128e8 /\ getr regs' 11 = Z_to_bv 64 0x1055c
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m R10.
  replace (0xaf81c : word) with (Z_to_bv 64 0xaf81c) by (apply bv_eq; reflexivity).
  replace (0x636a4 : word) with (Z_to_bv 64 0x636a4) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x636a4%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
Qed.

Lemma oc_K2a : forall (fx : FPState) regs m, getr regs 10 = Z_to_bv 64 3 ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf7a4 : word) m rom) (@mkst fx regs' (0x636a4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf7c0 /\ getr regs' 10 = Z_to_bv 64 0x113e5 /\ getr regs' 11 = Z_to_bv 64 0x1055c
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m R10.
  replace (0xaf7a4 : word) with (Z_to_bv 64 0xaf7a4) by (apply bv_eq; reflexivity).
  replace (0x636a4 : word) with (Z_to_bv 64 0x636a4) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x636a4%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
Qed.

Lemma oc_K3a : forall (fx : FPState) regs m, getr regs 10 = Z_to_bv 64 3 ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf7dc : word) m rom) (@mkst fx regs' (0x636a4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf7f8 /\ getr regs' 10 = Z_to_bv 64 0x1e6fe /\ getr regs' 11 = Z_to_bv 64 0x1055c
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m R10.
  replace (0xaf7dc : word) with (Z_to_bv 64 0xaf7dc) by (apply bv_eq; reflexivity).
  replace (0x636a4 : word) with (Z_to_bv 64 0x636a4) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x636a4%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
Qed.

Lemma oc_K4a : forall (fx : FPState) regs m, getr regs 10 = Z_to_bv 64 3 ->
  exists regs', msteps SEGS (@mkst fx regs (0xaf76c : word) m rom) (@mkst fx regs' (0x636a4 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf788 /\ getr regs' 10 = Z_to_bv 64 0x121b5 /\ getr regs' 11 = Z_to_bv 64 0x1055c
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m R10.
  replace (0xaf76c : word) with (Z_to_bv 64 0xaf76c) by (apply bv_eq; reflexivity).
  replace (0x636a4 : word) with (Z_to_bv 64 0x636a4) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m []) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 40%nat [0x636a4%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
Qed.

(* [comment removed for export] *)
Lemma oc_A : forall (fx : FPState) regs m (s pixs dbg : Z),
  (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 dbg ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf620 : word) m rom) (@mkst fx regs' (0xaf8a0 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf640 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 (s - 72)
    /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 dbg
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros fx regs m s pixs dbg Hs1 Hs2 R2 R10 R8 R18.
  replace (0xaf620 : word) with (Z_to_bv 64 0xaf620) by (apply bv_eq; reflexivity).
  replace (0xaf8a0 : word) with (Z_to_bv 64 0xaf8a0) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixs; dbg] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixs; dbg]) m [KRange (EVar 32) 96 (2 ^ 64 - 1)]%Z) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 60%nat [0xaf8a0%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
Qed.

(* [comment removed for export] *)
Lemma oc_B : forall (fx : FPState) regs m (pixs : Z),
  getr regs 8 = Z_to_bv 64 pixs ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf640 : word) m rom) (@mkst fx regs' (0x9713c : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf64c /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m pixs R8.
  replace (0xaf640 : word) with (Z_to_bv 64 0xaf640) by (apply bv_eq; reflexivity).
  replace (0x9713c : word) with (Z_to_bv 64 0x9713c) by (apply bv_eq; reflexivity).
  ex_entry regs [pixs] HR.
  assert (HK : know_ok SEGS (ex_env regs [pixs]) m []) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 60%nat [0x9713c%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
Qed.

(* [comment removed for export] *)
Lemma oc_C : forall (fx : FPState) regs m (s dbg : Z),
  (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 88)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 18 = Z_to_bv 64 dbg ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf64c : word) m rom) (@mkst fx regs' (0xaf8a0 : word) (O23LeptOcSegs.OCP m s (getr regs 10)) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf664 /\ getr regs' 10 = getr regs 10 /\ getr regs' 11 = Z_to_bv 64 (s - 76)
    /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 dbg
    /\ regs_agree (fun r => In r [1; 11; 12; 13; 14]%list) regs regs'.
Proof.
  intros fx regs m s dbg Hs1 Hs2 SOK R2 R18.
  replace (0xaf64c : word) with (Z_to_bv 64 0xaf64c) by (apply bv_eq; reflexivity).
  replace (0xaf8a0 : word) with (Z_to_bv 64 0xaf8a0) by (apply bv_eq; reflexivity).
  ex_entry regs [s; dbg] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; dbg]) m [KWr (SA (EVar 32) (-88)) 8; KRange (EVar 32) 96 (2 ^ 64 - 1)]%Z) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 60%nat [0xaf8a0%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [unfold O23LeptOcSegs.OCP; ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
Qed.

(* [comment removed for export] *)
Lemma oc_D : forall (fx : FPState) regs m (s : Z),
  (96 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 96) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf664 : word) m rom) (@mkst fx regs' (0x6df98 : word) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf66c /\ getr regs' 10 = Z_to_bv 64 (s - 88)
    /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof.
  intros fx regs m s Hs1 Hs2 R2.
  replace (0xaf664 : word) with (Z_to_bv 64 0xaf664) by (apply bv_eq; reflexivity).
  replace (0x6df98 : word) with (Z_to_bv 64 0x6df98) by (apply bv_eq; reflexivity).
  ex_entry regs [s] HR.
  assert (HK : know_ok SEGS (ex_env regs [s]) m [KRange (EVar 32) 96 (2 ^ 64 - 1)]%Z) by ex_know regs.
  ex_open HR HK Hms Hlf.
  ex_cont 60%nat [0x6df98%Z] (SCR [] [] []) HR Hlf HK Hms.
  lazymatch type of HR with regs_ok _ _ ?RR => exists RR end. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
Qed.

(* [comment removed for export] *)
Lemma oc_Ab : forall fr cs regs m (s d : Z) (ret v0 v1 v2 v3 v4 f0 f1 : word),
  (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 31)%Z -> d <> 1%Z ->
  rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 f0) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 f1) ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 d ->
  exists fr' regs',
    msteps SEGS (@mkst (mkFP fr cs) regs (0xaf620 : word) m rom) (@mkst (mkFP fr' cs) regs' (0x63740 : word) m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x1bb0e /\ getr regs' 11 = Z_to_bv 64 0x1055c
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20]%list) regs regs'.
Proof.
  intros fr cs regs m s d ret v0 v1 v2 v3 v4 f0 f1 Hs Hs64 Hd Hd1 RG RS R8 R16 R24 R32 R40 R48 R56 R64 H2 H10.
  replace (0xaf620 : word) with (Z_to_bv 64 0xaf620) by (apply bv_eq; reflexivity).
  replace (0x63740 : word) with (Z_to_bv 64 0x63740) by (apply bv_eq; reflexivity).
  pose proof I as FZ.
  ex_entryL [ret; v0; v1; v2; v3; v4; f0; f1] regs [s; d] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4; f0; f1] regs [s; d]) m
                 [KRange (EVar 40) 96 (2 ^ 64 - 1);
                  KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3);
                  KWord (SA (EVar 40) (-8)) 8 (EVar 0); KWord (SA (EVar 40) (-16)) 8 (EVar 1); KWord (SA (EVar 40) (-24)) 8 (EVar 2);
                  KWord (SA (EVar 40) (-32)) 8 (EVar 3); KWord (SA (EVar 40) (-40)) 8 (EVar 4); KWord (SA (EVar 40) (-48)) 8 (EVar 5);
                  KWord (SA (EVar 40) (-56)) 8 (EVar 6); KWord (SA (EVar 40) (-64)) 8 (EVar 7)]%Z)
    by (ex_know regs).
  pose proof HR as HRo. exb_open HR HK ST. clear HR.
  exb_drive 80%nat [0x63740%Z] (SCR [true] [] []) (@nil (nat * nat)) HK ST FZ.
  exb_exit ST R HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (@mkst (mkFP ?frx _) _ _ _ _) => exists frx, R end. split.
  - ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR); ex_agree HRo HR.
Qed.

Local Ltac ocfdl pc F D :=
  let f := eval vm_compute in (fetch_word SEGS (Z_to_bv 64 pc)) in
  lazymatch f with
  | Some ?w =>
      let l := word_lit (Z_to_bv 64 pc) in
      assert (F : fetch_word SEGS l = Some w) by (vm_cast_no_check (eq_refl (Some w)));
      let d := eval vm_compute in (decode_any w) in
      assert (D : decode_any w = d) by (vm_cast_no_check (eq_refl d))
  end.

Lemma oc_S : forall (fx : FPState) regs m (s o ent : Z),
  (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= o <= 4)%Z -> (0 <= ent < 2 ^ 30)%Z -> ret_ok (Z_to_bv 64 (0x1fcc0 + ent)) ->
  rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
  rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 o) ->
  rdn SEGS m (Z_to_bv 64 (0x1fcc0 + 4 * o)) 4 = Some (Z_to_le_bytes 4 ent) ->
  getr regs 2 = Z_to_bv 64 (s - 96) ->
  exists regs',
    msteps SEGS (@mkst fx regs (0xaf70c : word) m rom) (@mkst fx regs' (Z_to_bv 64 (0x1fcc0 + ent)) m rom)
    /\ getr regs' 10 = Z_to_bv 64 3
    /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m s o ent Hs Hs64 Ho He Hr RG RS Ro Rt R2.
  replace (0xaf70c : word) with (Z_to_bv 64 0xaf70c) by (apply bv_eq; reflexivity).
  assert (Ocase : (o = 0 \/ o = 1 \/ o = 2 \/ o = 3 \/ o = 4)%Z) by lia.
  destruct Ocase as [-> | [-> | [-> | [-> | ->]]]].
  - change (0x1fcc0 + 4 * 0)%Z with (0x1fcc0)%Z in Rt.
    ex_entry regs [s; ent] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; ent]) m
                   [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3);
                    KWord (SA (EVar 32) (-68)) 4 (ELit 0); KWord (SA (ELit 0) 0x1fcc0) 4 (EVar 33);
                    KRange (EVar 33) 0 (2 ^ 30 - 1)]%Z) by (ex_know regs).
    ex_run 60%nat [0xaf73c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    exists R'. split.
    + assert (Hm : msteps SEGS (@mkst fx regs (Z_to_bv 64 0xaf70c) m rom) (@mkst fx R' (Z_to_bv 64 0xaf73c) m rom)) by (ex_mem regs Hms).
      eapply msteps_trans; [exact Hm |].
      assert (A11 : getr R' 11 = Z_to_bv 64 (0x1fcc0 + ent)). { ex_reg regs HR'. Unshelve. all: rewrite ex_sx32 by lia; rewrite zbv_add; f_equal; lia. }
      ocfdl 0xaf73c%Z FJ DJ.
      eapply mst_step; [reflexivity | eapply step_jalr_gen; [exact FJ | reflexivity | exact DJ] |].
      match goal with |- msteps _ (@mkst _ (if ?c then _ else _) _ _ _) _ => replace c with true by (vm_compute; reflexivity) end.
      cbv beta iota.
      match goal with |- context [getr R' ?r] => replace (getr R' r) with (Z_to_bv 64 (0x1fcc0 + ent)) by (rewrite <- A11; f_equal; apply bv_eq; reflexivity) end.
      match goal with |- msteps _ (@mkst _ _ (jalr_tgt _ ?i) _ _) _ => replace i with 0%Z by (vm_compute; reflexivity) end.
      change (jalr_tgt (Z_to_bv 64 (0x1fcc0 + ent)) 0) with (v_jalr (Z_to_bv 64 (0x1fcc0 + ent)) 0).
      unfold ret_ok in Hr. rewrite Hr. apply mst_refl.
    + repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
  - change (0x1fcc0 + 4 * 1)%Z with (0x1fcc4)%Z in Rt.
    ex_entry regs [s; ent] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; ent]) m
                   [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3);
                    KWord (SA (EVar 32) (-68)) 4 (ELit 1); KWord (SA (ELit 0) 0x1fcc4) 4 (EVar 33);
                    KRange (EVar 33) 0 (2 ^ 30 - 1)]%Z) by (ex_know regs).
    ex_run 60%nat [0xaf73c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    exists R'. split.
    + assert (Hm : msteps SEGS (@mkst fx regs (Z_to_bv 64 0xaf70c) m rom) (@mkst fx R' (Z_to_bv 64 0xaf73c) m rom)) by (ex_mem regs Hms).
      eapply msteps_trans; [exact Hm |].
      assert (A11 : getr R' 11 = Z_to_bv 64 (0x1fcc0 + ent)). { ex_reg regs HR'. Unshelve. all: rewrite ex_sx32 by lia; rewrite zbv_add; f_equal; lia. }
      ocfdl 0xaf73c%Z FJ DJ.
      eapply mst_step; [reflexivity | eapply step_jalr_gen; [exact FJ | reflexivity | exact DJ] |].
      match goal with |- msteps _ (@mkst _ (if ?c then _ else _) _ _ _) _ => replace c with true by (vm_compute; reflexivity) end.
      cbv beta iota.
      match goal with |- context [getr R' ?r] => replace (getr R' r) with (Z_to_bv 64 (0x1fcc0 + ent)) by (rewrite <- A11; f_equal; apply bv_eq; reflexivity) end.
      match goal with |- msteps _ (@mkst _ _ (jalr_tgt _ ?i) _ _) _ => replace i with 0%Z by (vm_compute; reflexivity) end.
      change (jalr_tgt (Z_to_bv 64 (0x1fcc0 + ent)) 0) with (v_jalr (Z_to_bv 64 (0x1fcc0 + ent)) 0).
      unfold ret_ok in Hr. rewrite Hr. apply mst_refl.
    + repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
  - change (0x1fcc0 + 4 * 2)%Z with (0x1fcc8)%Z in Rt.
    ex_entry regs [s; ent] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; ent]) m
                   [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3);
                    KWord (SA (EVar 32) (-68)) 4 (ELit 2); KWord (SA (ELit 0) 0x1fcc8) 4 (EVar 33);
                    KRange (EVar 33) 0 (2 ^ 30 - 1)]%Z) by (ex_know regs).
    ex_run 60%nat [0xaf73c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    exists R'. split.
    + assert (Hm : msteps SEGS (@mkst fx regs (Z_to_bv 64 0xaf70c) m rom) (@mkst fx R' (Z_to_bv 64 0xaf73c) m rom)) by (ex_mem regs Hms).
      eapply msteps_trans; [exact Hm |].
      assert (A11 : getr R' 11 = Z_to_bv 64 (0x1fcc0 + ent)). { ex_reg regs HR'. Unshelve. all: rewrite ex_sx32 by lia; rewrite zbv_add; f_equal; lia. }
      ocfdl 0xaf73c%Z FJ DJ.
      eapply mst_step; [reflexivity | eapply step_jalr_gen; [exact FJ | reflexivity | exact DJ] |].
      match goal with |- msteps _ (@mkst _ (if ?c then _ else _) _ _ _) _ => replace c with true by (vm_compute; reflexivity) end.
      cbv beta iota.
      match goal with |- context [getr R' ?r] => replace (getr R' r) with (Z_to_bv 64 (0x1fcc0 + ent)) by (rewrite <- A11; f_equal; apply bv_eq; reflexivity) end.
      match goal with |- msteps _ (@mkst _ _ (jalr_tgt _ ?i) _ _) _ => replace i with 0%Z by (vm_compute; reflexivity) end.
      change (jalr_tgt (Z_to_bv 64 (0x1fcc0 + ent)) 0) with (v_jalr (Z_to_bv 64 (0x1fcc0 + ent)) 0).
      unfold ret_ok in Hr. rewrite Hr. apply mst_refl.
    + repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
  - change (0x1fcc0 + 4 * 3)%Z with (0x1fccc)%Z in Rt.
    ex_entry regs [s; ent] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; ent]) m
                   [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3);
                    KWord (SA (EVar 32) (-68)) 4 (ELit 3); KWord (SA (ELit 0) 0x1fccc) 4 (EVar 33);
                    KRange (EVar 33) 0 (2 ^ 30 - 1)]%Z) by (ex_know regs).
    ex_run 60%nat [0xaf73c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    exists R'. split.
    + assert (Hm : msteps SEGS (@mkst fx regs (Z_to_bv 64 0xaf70c) m rom) (@mkst fx R' (Z_to_bv 64 0xaf73c) m rom)) by (ex_mem regs Hms).
      eapply msteps_trans; [exact Hm |].
      assert (A11 : getr R' 11 = Z_to_bv 64 (0x1fcc0 + ent)). { ex_reg regs HR'. Unshelve. all: rewrite ex_sx32 by lia; rewrite zbv_add; f_equal; lia. }
      ocfdl 0xaf73c%Z FJ DJ.
      eapply mst_step; [reflexivity | eapply step_jalr_gen; [exact FJ | reflexivity | exact DJ] |].
      match goal with |- msteps _ (@mkst _ (if ?c then _ else _) _ _ _) _ => replace c with true by (vm_compute; reflexivity) end.
      cbv beta iota.
      match goal with |- context [getr R' ?r] => replace (getr R' r) with (Z_to_bv 64 (0x1fcc0 + ent)) by (rewrite <- A11; f_equal; apply bv_eq; reflexivity) end.
      match goal with |- msteps _ (@mkst _ _ (jalr_tgt _ ?i) _ _) _ => replace i with 0%Z by (vm_compute; reflexivity) end.
      change (jalr_tgt (Z_to_bv 64 (0x1fcc0 + ent)) 0) with (v_jalr (Z_to_bv 64 (0x1fcc0 + ent)) 0).
      unfold ret_ok in Hr. rewrite Hr. apply mst_refl.
    + repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
  - change (0x1fcc0 + 4 * 4)%Z with (0x1fcd0)%Z in Rt.
    ex_entry regs [s; ent] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; ent]) m
                   [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3);
                    KWord (SA (EVar 32) (-68)) 4 (ELit 4); KWord (SA (ELit 0) 0x1fcd0) 4 (EVar 33);
                    KRange (EVar 33) 0 (2 ^ 30 - 1)]%Z) by (ex_know regs).
    ex_run 60%nat [0xaf73c%Z] (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    exists R'. split.
    + assert (Hm : msteps SEGS (@mkst fx regs (Z_to_bv 64 0xaf70c) m rom) (@mkst fx R' (Z_to_bv 64 0xaf73c) m rom)) by (ex_mem regs Hms).
      eapply msteps_trans; [exact Hm |].
      assert (A11 : getr R' 11 = Z_to_bv 64 (0x1fcc0 + ent)). { ex_reg regs HR'. Unshelve. all: rewrite ex_sx32 by lia; rewrite zbv_add; f_equal; lia. }
      ocfdl 0xaf73c%Z FJ DJ.
      eapply mst_step; [reflexivity | eapply step_jalr_gen; [exact FJ | reflexivity | exact DJ] |].
      match goal with |- msteps _ (@mkst _ (if ?c then _ else _) _ _ _) _ => replace c with true by (vm_compute; reflexivity) end.
      cbv beta iota.
      match goal with |- context [getr R' ?r] => replace (getr R' r) with (Z_to_bv 64 (0x1fcc0 + ent)) by (rewrite <- A11; f_equal; apply bv_eq; reflexivity) end.
      match goal with |- msteps _ (@mkst _ _ (jalr_tgt _ ?i) _ _) _ => replace i with 0%Z by (vm_compute; reflexivity) end.
      change (jalr_tgt (Z_to_bv 64 (0x1fcc0 + ent)) 0) with (v_jalr (Z_to_bv 64 (0x1fcc0 + ent)) 0).
      unfold ret_ok in Hr. rewrite Hr. apply mst_refl.
    + repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

Lemma oc_X : forall fr cs regs m (s : Z) (ret v0 v1 v2 v3 v4 f0 f1 : word),
  (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 f0) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 f1) ->
  getr regs 2 = Z_to_bv 64 (s - 96) ->
  exists fr' regs',
    msteps SEGS (@mkst (mkFP fr cs) regs (0xaf874 : word) m rom) (@mkst (mkFP fr' cs) regs' ret m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = getr regs 10
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20]%list) regs regs'.
Proof.
  intros fr cs regs m s ret v0 v1 v2 v3 v4 f0 f1 Hs Hs64 Hret R8 R16 R24 R32 R40 R48 R56 R64 H2.
  replace (0xaf874 : word) with (Z_to_bv 64 0xaf874) by (apply bv_eq; reflexivity).
  pose proof I as FZ.
  ex_entryL [ret; v0; v1; v2; v3; v4; f0; f1] regs [s] HR.
  assert (HK : know_ok SEGS (ex_envL [ret; v0; v1; v2; v3; v4; f0; f1] regs [s]) m
                 [KRange (EVar 40) 96 (2 ^ 64 - 1);
                  KWord (SA (EVar 40) (-8)) 8 (EVar 0); KWord (SA (EVar 40) (-16)) 8 (EVar 1); KWord (SA (EVar 40) (-24)) 8 (EVar 2);
                  KWord (SA (EVar 40) (-32)) 8 (EVar 3); KWord (SA (EVar 40) (-40)) 8 (EVar 4); KWord (SA (EVar 40) (-48)) 8 (EVar 5);
                  KWord (SA (EVar 40) (-56)) 8 (EVar 6); KWord (SA (EVar 40) (-64)) 8 (EVar 7)]%Z)
    by (ex_know regs).
  pose proof HR as HRo. exb_open HR HK ST. clear HR.
  exb_adrive 20%nat 400%nat (@nil Z) (@nil (nat * nat)) HK ST FZ.
  exb_ret ST ret (eq_refl ret) Hret R HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (@mkst (mkFP ?frx _) _ _ _ _) => exists frx, R end. split.
  - ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR); ex_agree HRo HR.
Qed.

Lemma oc_XR : forall (fx : FPState) regs m,
  msteps SEGS (@mkst fx regs (0xaf818 : word) m rom) (@mkst fx regs (0xaf874 : word) m rom).
Proof.
  intros fx regs m.
  replace (0xaf818 : word) with (Z_to_bv 64 0xaf818) by (apply bv_eq; reflexivity). norm_pc.
  ocfdl 0xaf818%Z F1 D1.
  match type of D1 with decode_any ?w = Some (Jal ?z ?i, _) =>
    assert (D1' : decode_any w = Some (Jal 0 i, 4%Z)) by (rewrite D1; replace z with (0 : bv 5) by (apply bv_eq; reflexivity); reflexivity) end.
  chain_step; [reflexivity | eapply step_jal_x0; [exact F1 | reflexivity | exact D1'] | step_simpl].
  match goal with |- msteps _ (@mkst _ _ ?p _ _) (@mkst _ _ ?q _ _) => replace p with q by (apply bv_eq; vm_compute; reflexivity) end.
  apply mst_refl.
Qed.

Local Ltac oce_fpn := cbn [fp_regs fp_csr].
Local Ltac oce_zand F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite EQ; reflexivity).
Local Ltac oce_flw F D aa bb R :=
  chain_step; [ reflexivity | eapply fp_step_flw with (a := aa) (bs := bb); [exact F | reflexivity | exact D | gres; imm_norm; addr_tac | R] | step_simpl ];
  oce_fpn.
Local Ltac oce_fsw F D aa SOK :=
  chain_step; [ reflexivity | eapply fp_step_fsw with (a := aa); [exact F | reflexivity | exact D | gres; imm_norm; addr_tac | SOK] | step_simpl ];
  oce_fpn.
Local Ltac oce_fsgn F D := chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F | reflexivity | exact D] | step_simpl ]; oce_fpn.

(* [comment removed for export] *)
Lemma oc_E : forall fr cs regs m (s pup plf dbg : Z) (b0 b1 : list byte),
  (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (s <= pup)%Z -> (pup + 4 <= 2 ^ 64)%Z -> (s <= plf)%Z -> (plf + 4 <= 2 ^ 64)%Z ->
  (pup mod 4 = 0)%Z -> (plf mod 4 = 0)%Z ->
  (pup + 4 <= plf \/ plf + 4 <= pup)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 4 = Some b0 -> length b0 = 4%nat ->
  rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some b1 -> length b1 = 4%nat ->
  store_ok SEGS m (Z_to_bv 64 pup) 4 = true -> store_ok SEGS m (Z_to_bv 64 plf) 4 = true ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 18 = Z_to_bv 64 dbg -> getr regs 19 = Z_to_bv 64 plf -> getr regs 20 = Z_to_bv 64 pup ->
  exists fr' regs',
    msteps SEGS (@mkst (mkFP fr cs) regs (0xaf66c : word) m rom) (@mkst (mkFP fr' cs) regs' (0xafe34 : word) (O23LeptOcSegs.OCW m pup plf b0 b1) rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaf70c /\ getr regs' 10 = Z_to_bv 64 (s - 68) /\ getr regs' 11 = Z_to_bv 64 dbg
    /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Proof.
  intros fr cs regs m s pup plf dbg b0 b1 Hs1 Hs2 Hu1 Hu2 Hl1 Hl2 ALu ALl Hul RB0 LB0 RB1 LB1 SOu SOl R2 R18 R19 R20.
  do 2 eexists. split.
  - stepb_ft F_af66c D_af66c ltac:(condZ).
    oce_zand F_af670 D_af670 ALu.
    stepb_ft F_af674 D_af674 ltac:(condZ).
    oce_flw F_af678 D_af678 (Z_to_bv 64 (s - 72)) b0 ltac:(exact RB0).
    oce_fsw F_af67c D_af67c (Z_to_bv 64 pup) ltac:(exact SOu).
    rewrite fpv_get_same, (fpv_flw_bytes b0 LB0).
    stepb_ft F_af680 D_af680 ltac:(condZ).
    oce_zand F_af684 D_af684 ALl.
    stepb_ft F_af688 D_af688 ltac:(condZ).
    oce_flw F_af68c D_af68c (Z_to_bv 64 (s - 76)) b1
      ltac:(rewrite rdn_wbytes_out_Z by (rewrite ?LB0, ?LB1; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact RB1).
    oce_fsw F_af690 D_af690 (Z_to_bv 64 plf) ltac:(store_ok_peel; exact SOl).
    rewrite fpv_get_same, (fpv_flw_bytes b1 LB1).
    stepn F_af694 D_af694.
    oce_flw F_af6f4 D_af6f4 (Z_to_bv 64 (s - 72)) b0
      ltac:(rewrite !rdn_wbytes_out_Z by (rewrite ?LB0, ?LB1; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact RB0).
    zv F_af6f8 D_af6f8 (Z_to_bv 64 (s - 68)).
    oce_fsgn F_af6fc D_af6fc. oce_fsgn F_af700 D_af700.
    zv F_af704 D_af704 (Z_to_bv 64 dbg).
    stepn F_af708 D_af708.
    unfold O23LeptOcSegs.OCW. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

End Segs.

Section OcW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Instance ocw_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).

Variables (UDD_STK RK_udd : Z) (RB_udd : Z -> Z -> Z -> Z).
Hypothesis H_udd : pixUpDownDetect_contract UDD_STK RK_udd RB_udd.
Hypothesis RK_udd_nn : (0 <= RK_udd)%Z.
Hypothesis RB_udd_nn : forall w h cm, (0 <= RB_udd w h cm)%Z.
(* [comment removed for export] *)
Hypothesis RB_udd_le1 : forall w h cm, (RB_udd w h cm <= RB_udd w h 1)%Z.

Lemma str_oc_proc : str16 0x1055c 16.
Proof. str16_tac. Qed.

Lemma str_oc_err : str16 0x1bb0e 27.
Proof. str16_tac. Qed.

Lemma str_oc_f0 : str16 0x113ab 57.
Proof. str16_tac. Qed.

Lemma str_oc_f1 : str16 0x128e8 45.
Proof. str16_tac. Qed.

Lemma str_oc_f2 : str16 0x113e5 58.
Proof. str16_tac. Qed.

Lemma str_oc_f3 : str16 0x1e6fe 48.
Proof. str16_tac. Qed.

Lemma str_oc_f4 : str16 0x121b5 60.
Proof. str16_tac. Qed.

Lemma jt_oc0 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x1fcc0 + 4 * 0)) 4 = Some (Z_to_le_bytes 4 588416).
Proof. vm_refl_bv. Qed.

Lemma jt_oc1 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x1fcc0 + 4 * 1)) 4 = Some (Z_to_le_bytes 4 588636).
Proof. vm_refl_bv. Qed.

Lemma jt_oc2 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x1fcc0 + 4 * 2)) 4 = Some (Z_to_le_bytes 4 588516).
Proof. vm_refl_bv. Qed.

Lemma jt_oc3 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x1fcc0 + 4 * 3)) 4 = Some (Z_to_le_bytes 4 588572).
Proof. vm_refl_bv. Qed.

Lemma jt_oc4 : rdn SEGS (fun _ => None) (Z_to_bv 64 (0x1fcc0 + 4 * 4)) 4 = Some (Z_to_le_bytes 4 588460).
Proof. vm_refl_bv. Qed.

Lemma POSTM_wr_both : forall C A md (s : Z) (m m' : word -> option byte) (a : word) bs, Cok C -> W C A m md -> POSTM C A s m m' ->
  (c_top C - LSTK <= u a)%Z -> (u a + Z.of_nat (length bs) <= c_top C)%Z ->
  POSTM C A s (wbytes m a bs) (wbytes m' a bs).
Proof.
  intros C A md s m m' a bs CK HW [FR LV] H1 H2. pose proof CK as [T1 T2 T3 T4 T5].
  assert (HB : (u a + Z.of_nat (length bs) <= 2 ^ 64)%Z) by (pose proof (u64_range (c_sp0 C)); lia).
  assert (E : forall x : word, (forall y, y = x -> m' y = m y) -> wbytes m' a bs x = wbytes m a bs x).
  { intros x Ex. pose proof (u64_range x) as Ux.
    destruct (Z_lt_le_dec (u x) (u a)) as [L|L]; [| destruct (Z_lt_le_dec (u x) (u a + Z.of_nat (length bs))) as [L2|L2]].
    - rewrite !wbytes_outside by lia. apply Ex. reflexivity.
    - rewrite !wbytes_inside by lia. reflexivity.
    - rewrite !wbytes_outside by lia. apply Ex. reflexivity. }
  split.
  - intros x X1 X2 X3 X4 X5. apply E. intros y ->. apply FR; assumption.
  - intros q k i Lq Hi. apply E. intros y ->. apply (LV q k i Lq Hi).
Qed.

Definition OCC (m : word -> option byte) (s : Z) (ret v0 v1 v2 v3 v4 f0 f1 : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) /\
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v4) /\
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 f0) /\
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 f1).

Lemma OCC_OCF : forall m s ret regs fr, (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  OCC (O23LeptOcSegs.OCF m s ret regs fr) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
    (reg_get fr 8) (reg_get fr 9).
Proof. intros m s ret regs fr Hs Hs64. unfold OCC, O23LeptOcSegs.OCF. repeat split; rdn_chain. Qed.

Lemma OCC_pw : forall m m' s ret v0 v1 v2 v3 v4 f0 f1, (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (forall (b : Z) (n : nat), (s - 64 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m' (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n) ->
  OCC m s ret v0 v1 v2 v3 v4 f0 f1 -> OCC m' s ret v0 v1 v2 v3 v4 f0 f1.
Proof.
  intros m m' s ret v0 v1 v2 v3 v4 f0 f1 Hs Hs64 E (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  unfold OCC. repeat split; [rewrite <- C0 | rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5 | rewrite <- C6 | rewrite <- C7];
    apply E; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma pixt_new_eqA : forall C A A0 A' (m' : word -> option byte) (pixd w h d cd data : Z) (cv : cmapv),
  (forall q, live A0 q = live A q) -> pixt_new C A0 A' m' pixd w h d cd data cv -> pixt_new C A A' m' pixd w h d cd data cv.
Proof.
  intros C A A0 A' m' pixd w h d cd data cv E P. unfold pixt_new, cmres in *. setoid_rewrite E in P. exact P.
Qed.

Definition oc_res (C : lctx) (A A' : AS) (m' : word -> option byte) (regs' : bvmap 5 word) (cv : cmapv) : Prop :=
  (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
  \/ (exists pixd w' h' cd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok w' h' 1 /\ (1 <= w')%Z /\ (1 <= h')%Z /\
                                 pixt_new C A A' m' pixd w' h' 1 cd data cv).


Lemma oc_cs_glue : forall (regs rb : bvmap 5 word),
  getr rb 2 = getr regs 2 -> getr rb 8 = getr regs 8 -> getr rb 9 = getr regs 9 -> getr rb 18 = getr regs 18 ->
  getr rb 19 = getr regs 19 -> getr rb 20 = getr regs 20 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rb x = getr regs x) -> cs_kept regs rb.
Proof.
  intros regs rb G2 G8 G9 G18 G19 G20 K r Hr. unfold AllocIface.callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; try assumption; [apply K; cbn; tauto | apply K; cbn; tauto |].
  destruct (bv_eq_dec _ r 18%bv) as [->|N18]; [exact G18|].
  destruct (bv_eq_dec _ r 19%bv) as [->|N19]; [exact G19|].
  destruct (bv_eq_dec _ r 20%bv) as [->|N20]; [exact G20|].
  destruct (bv_eq_dec _ r 21%bv) as [->|N21]; [apply K; cbn [In]; auto 20|].
  destruct (bv_eq_dec _ r 22%bv) as [->|N22]; [apply K; cbn [In]; auto 20|].
  destruct (bv_eq_dec _ r 23%bv) as [->|N23]; [apply K; cbn [In]; auto 20|].
  destruct (bv_eq_dec _ r 24%bv) as [->|N24]; [apply K; cbn [In]; auto 20|].
  destruct (bv_eq_dec _ r 25%bv) as [->|N25]; [apply K; cbn [In]; auto 20|].
  destruct (bv_eq_dec _ r 26%bv) as [->|N26]; [apply K; cbn [In]; auto 20|].
  destruct (bv_eq_dec _ r 27%bv) as [->|N27]; [apply K; cbn [In]; auto 20|].
  exfalso.
  assert (bv_unsigned r <> 18%Z) by (intro X; apply N18; apply bv_eq; rewrite X; reflexivity).
  assert (bv_unsigned r <> 19%Z) by (intro X; apply N19; apply bv_eq; rewrite X; reflexivity).
  assert (bv_unsigned r <> 20%Z) by (intro X; apply N20; apply bv_eq; rewrite X; reflexivity).
  assert (bv_unsigned r <> 21%Z) by (intro X; apply N21; apply bv_eq; rewrite X; reflexivity).
  assert (bv_unsigned r <> 22%Z) by (intro X; apply N22; apply bv_eq; rewrite X; reflexivity).
  assert (bv_unsigned r <> 23%Z) by (intro X; apply N23; apply bv_eq; rewrite X; reflexivity).
  assert (bv_unsigned r <> 24%Z) by (intro X; apply N24; apply bv_eq; rewrite X; reflexivity).
  assert (bv_unsigned r <> 25%Z) by (intro X; apply N25; apply bv_eq; rewrite X; reflexivity).
  assert (bv_unsigned r <> 26%Z) by (intro X; apply N26; apply bv_eq; rewrite X; reflexivity).
  assert (bv_unsigned r <> 27%Z) by (intro X; apply N27; apply bv_eq; rewrite X; reflexivity).
  lia.
Qed.

Lemma oc_after_copy : forall fr cs C A A6 (m10 : word -> option byte) md vm6 r10 regs (s pixs w h cm datas : Z) (cv : cmapv)
    (ret f0 f1 : word) (M : word -> option byte) (S : TSet) (kR bR : Z),
  Cok C -> W C A6 m10 (with_vmmaps vm6 md) -> frm_zero cs -> (forall q, live A6 q = live A q) -> POSTM C A s M m10 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  getr r10 2 = Z_to_bv 64 (s - 96) -> getr r10 1 = Z_to_bv 64 0xaf874 -> getr r10 4 = Z_to_bv 64 0x1381d0 ->
  getr r10 10 = Z_to_bv 64 0 -> getr r10 11 = Z_to_bv 64 pixs ->
  PIXat m10 pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m10 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m10 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r10 x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s M m' -> oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) r10 (0x6eb5c : word) m10 al_rom) (with_vmmaps vm6 md)) S.
Proof.
  intros fr cs C A A6 m10 md vm6 r10 regs s pixs w h cm datas cv ret f0 f1 M S kR bR
    CK HW FZ E PM Hs16 Hlo Hhi Hret H2 R2 R1 R4 R10 R11 PX HOK Hw Hh Lp Ld HCM OC KEEP ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  assert (AM : (0 <= alloc_margin 256)%Z /\ (0 <= alloc_margin (4 * wpl_of w 1))%Z)
    by (split; [pose proof (alloc_margin_ge 256 ltac:(lia)) | pose proof (alloc_margin_ge (4 * wpl_of w 1)) as AG4; assert (0 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_pos; lia); specialize (AG4 ltac:(lia))]; lia).
  apply (pixCopy_szT_W (fx := mkFP fr cs) C A6 m10 (with_vmmaps vm6 md) r10 (s - 96) pixs w h 1 cm datas cv
           (Z_to_bv 64 0xaf874) S CK HW R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) R1 ltac:(red; apply bv_eq; reflexivity) R4 R10 R11 PX HOK Hw Hh
           ltac:(rewrite E; exact Lp) ltac:(rewrite E; exact Ld)
           ltac:(destruct HCM as [HC|(HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right; rewrite !E; auto])
           (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) ltac:(rewrite with_vmmaps_vmmaps; exact ROOM)
           ltac:(lia) ltac:(unfold RB_oc_arm; lia)).
  intros A' m' vm' regs' HW' CS' PM' RES ROOM'. rewrite with_vmmaps_twice in HW' |- *.
  assert (OC' : OCC m' s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m10 m' s); [lia | lia | | exact OC]. intros b n Hb Hn.
    rewrite <- p16_segs. apply (FRM_rdn_above C (s - 96) m10 m' b n CK (proj1 PM')); lia. }
  destruct OC' as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  assert (Q2 : getr regs' 2 = Z_to_bv 64 (s - 96)) by (rewrite (CS' 2%bv) by exB_cs; exact R2).
  destruct (oc_X al_rom fr cs regs' m' s ret _ _ _ _ _ f0 f1 ltac:(lia) ltac:(lia) Hret C0 C1 C2 C3 C4 C5 C6 C7 Q2)
    as (fr2 & r2 & RUN & G2 & G10 & G8 & G9 & G18 & G19 & G20 & AG).
  replace (Z_to_bv 64 0xaf874) with (0xaf874 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN |].
  apply (K fr2 cs A' m' vm' r2 HW' FZ).
  - apply oc_cs_glue; [rewrite G2, H2; reflexivity | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 |].
    intros x Hx. rewrite (AG x) by (cbn [In] in Hx |- *; intros X; repeat (destruct Hx as [<-|Hx]; [repeat (destruct X as [X|X]; [discriminate X|]); exact X|]); exact Hx).
    rewrite (CS' x) by (cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [first [exact cs3 | exact cs4 | exact cs21 | exact cs22 | exact cs23 | exact cs24 | exact cs25 | exact cs26 | exact cs27]|]); destruct Hx).
    apply KEEP. cbn [In] in Hx |- *. tauto.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A6 _ _ _ SUB). eapply POSTM_mono; [| exact PM']; lia.
  - destruct RES as [(Z0 & L0) | (pixd & cd & data & Z0 & PN)].
    + left. split; [rewrite (AG 10%bv) by notin_list; exact Z0 | intros q; rewrite L0; apply E].
    + right. exists pixd, w, h, cd, data. split; [rewrite (AG 10%bv) by notin_list; exact Z0|].
      split; [exact HOK|]. split; [exact Hw|]. split; [exact Hh|]. exact (pixt_new_eqA C A A6 A' m' pixd w h 1 cd data cv E PN).
  - apply (aroom_mono A' vm' _ _ kR bR ROOM'); unfold RB_oc_arm; lia.
Qed.

Lemma oc_hdr_rot : forall w h, hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok h w 1.
Proof.
  intros w h (DV & Hw & Hh & Hs) H1 H2. unfold hdr_ok. split; [exact DV|]. split; [lia|]. split; [lia|].
  assert (A1 : (wpl_of h 1 <= (20000 + 31) / 32)%Z) by (unfold wpl_of; apply Z.div_le_mono; lia).
  assert (A0 : (0 <= wpl_of h 1)%Z) by (unfold wpl_of; apply Z.div_pos; lia).
  assert (A2 : (wpl_of h 1 * w <= (20000 + 31) / 32 * 20000)%Z) by (apply Z.mul_le_mono_nonneg; lia).
  change ((20000 + 31) / 32 * 20000)%Z with 12500000%Z in A2. lia.
Qed.

Lemma oc_after_q1 : forall fr cs C A A6 (m10 : word -> option byte) md vm6 r10 regs (s pixs w h cm datas : Z) (cv : cmapv)
    (ret f0 f1 : word) (M : word -> option byte) (S : TSet) (kR bR : Z),
  Cok C -> W C A6 m10 (with_vmmaps vm6 md) -> frm_zero cs -> (forall q, live A6 q = live A q) -> POSTM C A s M m10 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  getr r10 2 = Z_to_bv 64 (s - 96) -> getr r10 1 = Z_to_bv 64 0xaf818 -> getr r10 4 = Z_to_bv 64 0x1381d0 ->
  getr r10 10 = Z_to_bv 64 pixs -> getr r10 11 = Z_to_bv 64 1 ->
  PIXat m10 pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m10 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m10 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r10 x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s M m' -> oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) r10 (0x97094 : word) m10 al_rom) (with_vmmaps vm6 md)) S.
Proof.
  intros fr cs C A A6 m10 md vm6 r10 regs s pixs w h cm datas cv ret f0 f1 M S kR bR
    CK HW FZ E PM Hs16 Hlo Hhi Hret H2 R2 R1 R4 R10 R11 PX HOK Hw Hh Lp Ld HCM OC KEEP ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  assert (AM : (0 <= alloc_margin 256)%Z /\ (0 <= alloc_margin (4 * wpl_of w 1))%Z)
    by (split; [pose proof (alloc_margin_ge 256 ltac:(lia)) | pose proof (alloc_margin_ge (4 * wpl_of w 1)) as AG4; assert (0 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_pos; lia); specialize (AG4 ltac:(lia))]; lia).
  apply (pixRotateOrth_q1_W (fx := mkFP fr cs) C A6 m10 (with_vmmaps vm6 md) r10 (s - 96) pixs 1 w h cm datas cv
           (Z_to_bv 64 0xaf818) S CK HW R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold R90_STACK, LSF; lia) ltac:(lia) R1 ltac:(red; apply bv_eq; reflexivity) R4 R10 R11 PX HOK Hw Hh
           ltac:(rewrite E; exact Lp) ltac:(rewrite E; exact Ld)
           ltac:(destruct HCM as [HC|(HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right; rewrite !E; auto])
           (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) ltac:(rewrite with_vmmaps_vmmaps; exact ROOM)
           ltac:(unfold RK_pixcopy in *; lia) ltac:(unfold RB_oc_arm; lia)).
  intros A' m' vm' regs' HW' CS' PM' RES ROOM'. rewrite with_vmmaps_twice in HW' |- *.
  assert (OC' : OCC m' s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m10 m' s); [lia | lia | | exact OC]. intros b n Hb Hn.
    rewrite <- p16_segs. apply (FRM_rdn_above C (s - 96) m10 m' b n CK (proj1 PM')); lia. }
  destruct OC' as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  assert (Q2 : getr regs' 2 = Z_to_bv 64 (s - 96)) by (rewrite (CS' 2%bv) by exB_cs; exact R2).
  destruct (oc_X al_rom fr cs regs' m' s ret _ _ _ _ _ f0 f1 ltac:(lia) ltac:(lia) Hret C0 C1 C2 C3 C4 C5 C6 C7 Q2)
    as (fr2 & r2 & RUN & G2 & G10 & G8 & G9 & G18 & G19 & G20 & AG).
  replace (Z_to_bv 64 0xaf818) with (0xaf818 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact (oc_XR al_rom (mkFP fr cs) regs' m') |].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN |].
  apply (K fr2 cs A' m' vm' r2 HW' FZ).
  - apply oc_cs_glue; [rewrite G2, H2; reflexivity | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 |].
    intros x Hx. rewrite (AG x) by (cbn [In] in Hx |- *; intros X; repeat (destruct Hx as [<-|Hx]; [repeat (destruct X as [X|X]; [discriminate X|]); exact X|]); exact Hx).
    rewrite (CS' x) by (cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [first [exact cs3 | exact cs4 | exact cs21 | exact cs22 | exact cs23 | exact cs24 | exact cs25 | exact cs26 | exact cs27]|]); destruct Hx).
    apply KEEP. cbn [In] in Hx |- *. tauto.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A6 _ _ _ SUB). eapply POSTM_mono; [| exact PM']; lia.
  - destruct RES as [(Z0 & L0) | (pixd & cd & data & Z0 & PN)].
    + left. split; [rewrite (AG 10%bv) by notin_list; exact Z0 | intros q; rewrite L0; apply E].
    + right. exists pixd, h, w, cd, data. split; [rewrite (AG 10%bv) by notin_list; exact Z0|].
      split; [apply oc_hdr_rot; assumption|]. split; [lia|]. split; [lia|]. exact (pixt_new_eqA C A A6 A' m' pixd h w 1 cd data cv E PN).
  - apply (aroom_mono A' vm' _ _ kR bR ROOM'); unfold RB_oc_arm, RK_pixcopy in *; lia.
Qed.

Lemma oc_after_q2 : forall fr cs C A A6 (m10 : word -> option byte) md vm6 r10 regs (s pixs w h cm datas : Z) (cv : cmapv)
    (ret f0 f1 : word) (M : word -> option byte) (S : TSet) (kR bR : Z),
  Cok C -> W C A6 m10 (with_vmmaps vm6 md) -> frm_zero cs -> (forall q, live A6 q = live A q) -> POSTM C A s M m10 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  getr r10 2 = Z_to_bv 64 (s - 96) -> getr r10 1 = Z_to_bv 64 0xaf818 -> getr r10 4 = Z_to_bv 64 0x1381d0 ->
  getr r10 10 = Z_to_bv 64 pixs -> getr r10 11 = Z_to_bv 64 2 ->
  PIXat m10 pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m10 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m10 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r10 x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s M m' -> oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) r10 (0x97094 : word) m10 al_rom) (with_vmmaps vm6 md)) S.
Proof.
  intros fr cs C A A6 m10 md vm6 r10 regs s pixs w h cm datas cv ret f0 f1 M S kR bR
    CK HW FZ E PM Hs16 Hlo Hhi Hret H2 R2 R1 R4 R10 R11 PX HOK Hw Hh Lp Ld HCM OC KEEP ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  assert (AM : (0 <= alloc_margin 256)%Z /\ (0 <= alloc_margin (4 * wpl_of w 1))%Z)
    by (split; [pose proof (alloc_margin_ge 256 ltac:(lia)) | pose proof (alloc_margin_ge (4 * wpl_of w 1)) as AG4; assert (0 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_pos; lia); specialize (AG4 ltac:(lia))]; lia).
  apply (pixRotateOrth_q2_W (fx := mkFP fr cs) C A6 m10 (with_vmmaps vm6 md) r10 (s - 96) pixs 1 w h cm datas cv
           (Z_to_bv 64 0xaf818) S CK HW R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold R180_STACK, LSF; lia) ltac:(lia) R1 ltac:(red; apply bv_eq; reflexivity) R4 R10 R11 PX HOK Hw Hh
           ltac:(rewrite E; exact Lp) ltac:(rewrite E; exact Ld)
           ltac:(destruct HCM as [HC|(HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right; rewrite !E; auto])
           (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) ltac:(rewrite with_vmmaps_vmmaps; exact ROOM)
           ltac:(unfold RK_pixcopy in *; lia) ltac:(unfold RB_oc_arm; lia)).
  intros A' m' vm' regs' HW' CS' PM' RES ROOM'. rewrite with_vmmaps_twice in HW' |- *.
  assert (OC' : OCC m' s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m10 m' s); [lia | lia | | exact OC]. intros b n Hb Hn.
    rewrite <- p16_segs. apply (FRM_rdn_above C (s - 96) m10 m' b n CK (proj1 PM')); lia. }
  destruct OC' as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  assert (Q2 : getr regs' 2 = Z_to_bv 64 (s - 96)) by (rewrite (CS' 2%bv) by exB_cs; exact R2).
  destruct (oc_X al_rom fr cs regs' m' s ret _ _ _ _ _ f0 f1 ltac:(lia) ltac:(lia) Hret C0 C1 C2 C3 C4 C5 C6 C7 Q2)
    as (fr2 & r2 & RUN & G2 & G10 & G8 & G9 & G18 & G19 & G20 & AG).
  replace (Z_to_bv 64 0xaf818) with (0xaf818 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact (oc_XR al_rom (mkFP fr cs) regs' m') |].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN |].
  apply (K fr2 cs A' m' vm' r2 HW' FZ).
  - apply oc_cs_glue; [rewrite G2, H2; reflexivity | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 |].
    intros x Hx. rewrite (AG x) by (cbn [In] in Hx |- *; intros X; repeat (destruct Hx as [<-|Hx]; [repeat (destruct X as [X|X]; [discriminate X|]); exact X|]); exact Hx).
    rewrite (CS' x) by (cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [first [exact cs3 | exact cs4 | exact cs21 | exact cs22 | exact cs23 | exact cs24 | exact cs25 | exact cs26 | exact cs27]|]); destruct Hx).
    apply KEEP. cbn [In] in Hx |- *. tauto.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A6 _ _ _ SUB). eapply POSTM_mono; [| exact PM']; lia.
  - destruct RES as [(Z0 & L0) | (pixd & cd & data & Z0 & PN)].
    + left. split; [rewrite (AG 10%bv) by notin_list; exact Z0 | intros q; rewrite L0; apply E].
    + right. exists pixd, w, h, cd, data. split; [rewrite (AG 10%bv) by notin_list; exact Z0|].
      split; [exact HOK|]. split; [lia|]. split; [lia|]. exact (pixt_new_eqA C A A6 A' m' pixd w h 1 cd data cv E PN).
  - apply (aroom_mono A' vm' _ _ kR bR ROOM'); unfold RB_oc_arm, RK_pixcopy in *; lia.
Qed.

Lemma oc_after_q3 : forall fr cs C A A6 (m10 : word -> option byte) md vm6 r10 regs (s pixs w h cm datas : Z) (cv : cmapv)
    (ret f0 f1 : word) (M : word -> option byte) (S : TSet) (kR bR : Z),
  Cok C -> W C A6 m10 (with_vmmaps vm6 md) -> frm_zero cs -> (forall q, live A6 q = live A q) -> POSTM C A s M m10 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  getr r10 2 = Z_to_bv 64 (s - 96) -> getr r10 1 = Z_to_bv 64 0xaf818 -> getr r10 4 = Z_to_bv 64 0x1381d0 ->
  getr r10 10 = Z_to_bv 64 pixs -> getr r10 11 = Z_to_bv 64 3 ->
  PIXat m10 pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m10 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m10 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r10 x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s M m' -> oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) r10 (0x97094 : word) m10 al_rom) (with_vmmaps vm6 md)) S.
Proof.
  intros fr cs C A A6 m10 md vm6 r10 regs s pixs w h cm datas cv ret f0 f1 M S kR bR
    CK HW FZ E PM Hs16 Hlo Hhi Hret H2 R2 R1 R4 R10 R11 PX HOK Hw Hh Lp Ld HCM OC KEEP ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  assert (AM : (0 <= alloc_margin 256)%Z /\ (0 <= alloc_margin (4 * wpl_of w 1))%Z)
    by (split; [pose proof (alloc_margin_ge 256 ltac:(lia)) | pose proof (alloc_margin_ge (4 * wpl_of w 1)) as AG4; assert (0 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_pos; lia); specialize (AG4 ltac:(lia))]; lia).
  apply (pixRotateOrth_q3_W (fx := mkFP fr cs) C A6 m10 (with_vmmaps vm6 md) r10 (s - 96) pixs 1 w h cm datas cv
           (Z_to_bv 64 0xaf818) S CK HW R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold R90_STACK, LSF; lia) ltac:(lia) R1 ltac:(red; apply bv_eq; reflexivity) R4 R10 R11 PX HOK Hw Hh
           ltac:(rewrite E; exact Lp) ltac:(rewrite E; exact Ld)
           ltac:(destruct HCM as [HC|(HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right; rewrite !E; auto])
           (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) ltac:(rewrite with_vmmaps_vmmaps; exact ROOM)
           ltac:(unfold RK_pixcopy in *; lia) ltac:(unfold RB_oc_arm; lia)).
  intros A' m' vm' regs' HW' CS' PM' RES ROOM'. rewrite with_vmmaps_twice in HW' |- *.
  assert (OC' : OCC m' s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m10 m' s); [lia | lia | | exact OC]. intros b n Hb Hn.
    rewrite <- p16_segs. apply (FRM_rdn_above C (s - 96) m10 m' b n CK (proj1 PM')); lia. }
  destruct OC' as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  assert (Q2 : getr regs' 2 = Z_to_bv 64 (s - 96)) by (rewrite (CS' 2%bv) by exB_cs; exact R2).
  destruct (oc_X al_rom fr cs regs' m' s ret _ _ _ _ _ f0 f1 ltac:(lia) ltac:(lia) Hret C0 C1 C2 C3 C4 C5 C6 C7 Q2)
    as (fr2 & r2 & RUN & G2 & G10 & G8 & G9 & G18 & G19 & G20 & AG).
  replace (Z_to_bv 64 0xaf818) with (0xaf818 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact (oc_XR al_rom (mkFP fr cs) regs' m') |].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN |].
  apply (K fr2 cs A' m' vm' r2 HW' FZ).
  - apply oc_cs_glue; [rewrite G2, H2; reflexivity | exact G8 | exact G9 | exact G18 | exact G19 | exact G20 |].
    intros x Hx. rewrite (AG x) by (cbn [In] in Hx |- *; intros X; repeat (destruct Hx as [<-|Hx]; [repeat (destruct X as [X|X]; [discriminate X|]); exact X|]); exact Hx).
    rewrite (CS' x) by (cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [first [exact cs3 | exact cs4 | exact cs21 | exact cs22 | exact cs23 | exact cs24 | exact cs25 | exact cs26 | exact cs27]|]); destruct Hx).
    apply KEEP. cbn [In] in Hx |- *. tauto.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A6 _ _ _ SUB). eapply POSTM_mono; [| exact PM']; lia.
  - destruct RES as [(Z0 & L0) | (pixd & cd & data & Z0 & PN)].
    + left. split; [rewrite (AG 10%bv) by notin_list; exact Z0 | intros q; rewrite L0; apply E].
    + right. exists pixd, h, w, cd, data. split; [rewrite (AG 10%bv) by notin_list; exact Z0|].
      split; [apply oc_hdr_rot; assumption|]. split; [lia|]. split; [lia|]. exact (pixt_new_eqA C A A6 A' m' pixd h w 1 cd data cv E PN).
  - apply (aroom_mono A' vm' _ _ kR bR ROOM'); unfold RB_oc_arm, RK_pixcopy in *; lia.
Qed.
Local Ltac oca_kc := repeat match goal with H : _ |- _ => clear H end.
Ltac oca_cs := first [exact cs2 | exact cs3 | exact cs4 | exact cs8 | exact cs9 | exact cs18 | exact cs19 | exact cs20
  | exact cs21 | exact cs22 | exact cs23 | exact cs24 | exact cs25 | exact cs26 | exact cs27].
Ltac oca_g := repeat match goal with
  | CS : cs_kept ?a ?b |- getr ?b ?x = _ => rewrite (cs_kept_get a b x CS) by oca_cs
  | AG : regs_agree _ ?a ?b |- getr ?b ?x = _ => rewrite (AG x ltac:(notin_lit))
  end; first [assumption | reflexivity | match goal with KP : forall x, In x _ -> getr _ x = getr _ x |- _ => apply KP; cbn; tauto end].

Lemma oc_arm_q1 : forall fr cs C A A6 (m8 Mr : word -> option byte) md vm6 rS regs (s pixs prot w h cm datas : Z) (cv : cmapv)
    (ret f0 f1 : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A6 m8 (with_vmmaps vm6 md) -> frm_zero cs -> (forall q, live A6 q = live A q) -> POSTM C A s Mr m8 -> W C A Mr md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  (s <= prot)%Z -> (prot + 4 <= c_top C)%Z -> (prot mod 4 = 0)%Z ->
  getr rS 2 = Z_to_bv 64 (s - 96) -> getr rS 4 = Z_to_bv 64 0x1381d0 -> getr rS 8 = Z_to_bv 64 pixs -> getr rS 9 = Z_to_bv 64 prot ->
  getr rS 10 = Z_to_bv 64 3 ->
  PIXat m8 pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m8 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m8 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rS x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s (wr4 Mr prot 90) m' -> oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) rS (0xaf7a4 : word) m8 al_rom) (with_vmmaps vm6 md)) S.
Proof.
  intros fr cs C A A6 m8 Mr md vm6 rS regs s pixs prot w h cm datas cv ret f0 f1 S kR bR
    CK HW FZ E PM HWr Hs16 Hlo Hhi Hret H2 Hp1 Hp2 Hp4 R2 R4 R8 R9 R10 PX HOK Hw Hh Lp Ld HCM OC KEEP ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  destruct (oc_K2a al_rom (mkFP fr cs) rS m8 R10) as (r11 & RUN11 & M1' & M10' & M11' & AG11).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN11 |].
  apply (lept_stderr1P8_W (fx := mkFP fr cs) C A6 m8 (with_vmmaps vm6 md) r11 (s - 96) 0x113e5 0x1055c 58 16 (Z_to_bv 64 0xaf7c0) S CK HW
           ltac:(oca_g) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
           M1' ltac:(red; apply bv_eq; reflexivity) M10' M11' ltac:(oca_kc; cbn; tauto) str_oc_f2 str_oc_proc).
  intros m9 r12 HW9 OUT9 GR9 CS12. unfold LSF in OUT9.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => let v := eval vm_compute in (bv_unsigned pc) in
    replace pc with (@BV 64 v I : word) by (apply bv_eq; reflexivity) end.
  destruct (oc_K2b al_rom (mkFP fr cs) r12 m9 prot pixs ltac:(lia) ltac:(lia) Hp4
              (W_sok_win C A6 m9 _ prot 4 CK HW9 ltac:(lia) ltac:(cbn; lia)) ltac:(oca_g) ltac:(oca_g))
    as (r13 & RUN13 & N1 & N10 & N11 & AG13).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN13 |].
  assert (HW10 : W C A6 (wr4 m9 prot 90) (with_vmmaps vm6 md)).
  { unfold wr4. apply W_store_win; [exact CK | exact HW9 | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (PM9 : POSTM C A s Mr m9).
  { eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A6 _ _ _ SUB).
    apply (POSTM_range C A6 m8 _ m9 (s - 96 - 3376) (s - 96) s CK HW OUT9); lia. }
  assert (PM10 : POSTM C A s (wr4 Mr prot 90) (wr4 m9 prot 90)).
  { unfold wr4. apply (POSTM_wr_both C A md s Mr m9 (Z_to_bv 64 prot) _ CK HWr PM9); [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (KEEPh : forall x : word, ~ (s - 96 - 3376 <= u x < s - 96)%Z -> ~ (prot <= u x < prot + 4)%Z -> wr4 m9 prot 90 x = m8 x).
  { intros x Hx Hq. unfold wr4. rewrite MemSplit.wbytes_outside by (rewrite ?u_Z2bv by lia; zlen; lia).
    apply OUT9. lia. }
  assert (HEAP : forall (q : word) k (x : word), live A6 q = Some k -> (u q <= u x < u q + k)%Z -> wr4 m9 prot 90 x = m8 x).
  { intros q k x Lq Hx. destruct (blk_byte C A6 m8 _ q k x CK HW Lq Hx) as (_ & _ & _ & NW & _).
    assert (NW' : ~ (c_top C - LSTK <= u x < c_top C)%Z) by exact NW.
    apply KEEPh; lia. }
  assert (PX10 : PIXat (wr4 m9 prot 90) pixs (hdv w h 1 cm datas)).
  { pose proof PX as (Hp0 & Hp64 & _).
    apply (PIXat_frame m8 _ pixs _ PX). intros x Hx. apply (HEAP (Z_to_bv 64 pixs) 64%Z x); [rewrite E; exact Lp | rewrite u_Z2bv by lia; lia]. }
  assert (HCM10 : cm = 0%Z \/ (CMAPat (wr4 m9 prot 90) cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                                live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [HC | (HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right].
    refine (conj _ (conj HC2 (conj HC3 HC4))). pose proof HC1 as (Hc0 & Hc24 & _).
    apply (CMAPat_frame m8 _ cm cv HC1). intros x Hx. apply (HEAP (Z_to_bv 64 cm) 24%Z x); [rewrite E; exact HC3 | rewrite u_Z2bv by lia; lia]. }
  assert (OC10 : OCC (wr4 m9 prot 90) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m8 _ s); [lia | lia | | exact OC]. intros b n Hb Hn. destruct n as [|n]; [reflexivity|].
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply KEEPh; lia. }
  apply (oc_after_q1 fr cs C A A6 (wr4 m9 prot 90) md vm6 r13 regs s pixs w h cm datas cv ret f0 f1 (wr4 Mr prot 90) S kR bR
           CK HW10 FZ E PM10 Hs16 Hlo Hhi Hret H2 ltac:(oca_g) ltac:(rewrite N1; reflexivity) ltac:(oca_g) N10 N11
           PX10 HOK Hw Hh Lp Ld HCM10 OC10
           ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                 destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; oca_g)
           ROOM HkR HbR K).
Qed.

Lemma oc_arm_q2 : forall fr cs C A A6 (m8 Mr : word -> option byte) md vm6 rS regs (s pixs prot w h cm datas : Z) (cv : cmapv)
    (ret f0 f1 : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A6 m8 (with_vmmaps vm6 md) -> frm_zero cs -> (forall q, live A6 q = live A q) -> POSTM C A s Mr m8 -> W C A Mr md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  (s <= prot)%Z -> (prot + 4 <= c_top C)%Z -> (prot mod 4 = 0)%Z ->
  getr rS 2 = Z_to_bv 64 (s - 96) -> getr rS 4 = Z_to_bv 64 0x1381d0 -> getr rS 8 = Z_to_bv 64 pixs -> getr rS 9 = Z_to_bv 64 prot ->
  getr rS 10 = Z_to_bv 64 3 ->
  PIXat m8 pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m8 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m8 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rS x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s (wr4 Mr prot 180) m' -> oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) rS (0xaf7dc : word) m8 al_rom) (with_vmmaps vm6 md)) S.
Proof.
  intros fr cs C A A6 m8 Mr md vm6 rS regs s pixs prot w h cm datas cv ret f0 f1 S kR bR
    CK HW FZ E PM HWr Hs16 Hlo Hhi Hret H2 Hp1 Hp2 Hp4 R2 R4 R8 R9 R10 PX HOK Hw Hh Lp Ld HCM OC KEEP ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  destruct (oc_K3a al_rom (mkFP fr cs) rS m8 R10) as (r11 & RUN11 & M1' & M10' & M11' & AG11).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN11 |].
  apply (lept_stderr1P8_W (fx := mkFP fr cs) C A6 m8 (with_vmmaps vm6 md) r11 (s - 96) 0x1e6fe 0x1055c 48 16 (Z_to_bv 64 0xaf7f8) S CK HW
           ltac:(oca_g) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
           M1' ltac:(red; apply bv_eq; reflexivity) M10' M11' ltac:(oca_kc; cbn; tauto) str_oc_f3 str_oc_proc).
  intros m9 r12 HW9 OUT9 GR9 CS12. unfold LSF in OUT9.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => let v := eval vm_compute in (bv_unsigned pc) in
    replace pc with (@BV 64 v I : word) by (apply bv_eq; reflexivity) end.
  destruct (oc_K3b al_rom (mkFP fr cs) r12 m9 prot pixs ltac:(lia) ltac:(lia) Hp4
              (W_sok_win C A6 m9 _ prot 4 CK HW9 ltac:(lia) ltac:(cbn; lia)) ltac:(oca_g) ltac:(oca_g))
    as (r13 & RUN13 & N1 & N10 & N11 & AG13).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN13 |].
  assert (HW10 : W C A6 (wr4 m9 prot 180) (with_vmmaps vm6 md)).
  { unfold wr4. apply W_store_win; [exact CK | exact HW9 | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (PM9 : POSTM C A s Mr m9).
  { eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A6 _ _ _ SUB).
    apply (POSTM_range C A6 m8 _ m9 (s - 96 - 3376) (s - 96) s CK HW OUT9); lia. }
  assert (PM10 : POSTM C A s (wr4 Mr prot 180) (wr4 m9 prot 180)).
  { unfold wr4. apply (POSTM_wr_both C A md s Mr m9 (Z_to_bv 64 prot) _ CK HWr PM9); [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (KEEPh : forall x : word, ~ (s - 96 - 3376 <= u x < s - 96)%Z -> ~ (prot <= u x < prot + 4)%Z -> wr4 m9 prot 180 x = m8 x).
  { intros x Hx Hq. unfold wr4. rewrite MemSplit.wbytes_outside by (rewrite ?u_Z2bv by lia; zlen; lia).
    apply OUT9. lia. }
  assert (HEAP : forall (q : word) k (x : word), live A6 q = Some k -> (u q <= u x < u q + k)%Z -> wr4 m9 prot 180 x = m8 x).
  { intros q k x Lq Hx. destruct (blk_byte C A6 m8 _ q k x CK HW Lq Hx) as (_ & _ & _ & NW & _).
    assert (NW' : ~ (c_top C - LSTK <= u x < c_top C)%Z) by exact NW.
    apply KEEPh; lia. }
  assert (PX10 : PIXat (wr4 m9 prot 180) pixs (hdv w h 1 cm datas)).
  { pose proof PX as (Hp0 & Hp64 & _).
    apply (PIXat_frame m8 _ pixs _ PX). intros x Hx. apply (HEAP (Z_to_bv 64 pixs) 64%Z x); [rewrite E; exact Lp | rewrite u_Z2bv by lia; lia]. }
  assert (HCM10 : cm = 0%Z \/ (CMAPat (wr4 m9 prot 180) cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                                live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [HC | (HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right].
    refine (conj _ (conj HC2 (conj HC3 HC4))). pose proof HC1 as (Hc0 & Hc24 & _).
    apply (CMAPat_frame m8 _ cm cv HC1). intros x Hx. apply (HEAP (Z_to_bv 64 cm) 24%Z x); [rewrite E; exact HC3 | rewrite u_Z2bv by lia; lia]. }
  assert (OC10 : OCC (wr4 m9 prot 180) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m8 _ s); [lia | lia | | exact OC]. intros b n Hb Hn. destruct n as [|n]; [reflexivity|].
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply KEEPh; lia. }
  apply (oc_after_q2 fr cs C A A6 (wr4 m9 prot 180) md vm6 r13 regs s pixs w h cm datas cv ret f0 f1 (wr4 Mr prot 180) S kR bR
           CK HW10 FZ E PM10 Hs16 Hlo Hhi Hret H2 ltac:(oca_g) ltac:(rewrite N1; reflexivity) ltac:(oca_g) N10 N11
           PX10 HOK Hw Hh Lp Ld HCM10 OC10
           ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                 destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; oca_g)
           ROOM HkR HbR K).
Qed.

Lemma oc_arm_q3 : forall fr cs C A A6 (m8 Mr : word -> option byte) md vm6 rS regs (s pixs prot w h cm datas : Z) (cv : cmapv)
    (ret f0 f1 : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A6 m8 (with_vmmaps vm6 md) -> frm_zero cs -> (forall q, live A6 q = live A q) -> POSTM C A s Mr m8 -> W C A Mr md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  (s <= prot)%Z -> (prot + 4 <= c_top C)%Z -> (prot mod 4 = 0)%Z ->
  getr rS 2 = Z_to_bv 64 (s - 96) -> getr rS 4 = Z_to_bv 64 0x1381d0 -> getr rS 8 = Z_to_bv 64 pixs -> getr rS 9 = Z_to_bv 64 prot ->
  getr rS 10 = Z_to_bv 64 3 ->
  PIXat m8 pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m8 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m8 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rS x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s (wr4 Mr prot 270) m' -> oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) rS (0xaf76c : word) m8 al_rom) (with_vmmaps vm6 md)) S.
Proof.
  intros fr cs C A A6 m8 Mr md vm6 rS regs s pixs prot w h cm datas cv ret f0 f1 S kR bR
    CK HW FZ E PM HWr Hs16 Hlo Hhi Hret H2 Hp1 Hp2 Hp4 R2 R4 R8 R9 R10 PX HOK Hw Hh Lp Ld HCM OC KEEP ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  destruct (oc_K4a al_rom (mkFP fr cs) rS m8 R10) as (r11 & RUN11 & M1' & M10' & M11' & AG11).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN11 |].
  apply (lept_stderr1P8_W (fx := mkFP fr cs) C A6 m8 (with_vmmaps vm6 md) r11 (s - 96) 0x121b5 0x1055c 60 16 (Z_to_bv 64 0xaf788) S CK HW
           ltac:(oca_g) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
           M1' ltac:(red; apply bv_eq; reflexivity) M10' M11' ltac:(oca_kc; cbn; tauto) str_oc_f4 str_oc_proc).
  intros m9 r12 HW9 OUT9 GR9 CS12. unfold LSF in OUT9.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => let v := eval vm_compute in (bv_unsigned pc) in
    replace pc with (@BV 64 v I : word) by (apply bv_eq; reflexivity) end.
  destruct (oc_K4b al_rom (mkFP fr cs) r12 m9 prot pixs ltac:(lia) ltac:(lia) Hp4
              (W_sok_win C A6 m9 _ prot 4 CK HW9 ltac:(lia) ltac:(cbn; lia)) ltac:(oca_g) ltac:(oca_g))
    as (r13 & RUN13 & N1 & N10 & N11 & AG13).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN13 |].
  assert (HW10 : W C A6 (wr4 m9 prot 270) (with_vmmaps vm6 md)).
  { unfold wr4. apply W_store_win; [exact CK | exact HW9 | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (PM9 : POSTM C A s Mr m9).
  { eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A6 _ _ _ SUB).
    apply (POSTM_range C A6 m8 _ m9 (s - 96 - 3376) (s - 96) s CK HW OUT9); lia. }
  assert (PM10 : POSTM C A s (wr4 Mr prot 270) (wr4 m9 prot 270)).
  { unfold wr4. apply (POSTM_wr_both C A md s Mr m9 (Z_to_bv 64 prot) _ CK HWr PM9); [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (KEEPh : forall x : word, ~ (s - 96 - 3376 <= u x < s - 96)%Z -> ~ (prot <= u x < prot + 4)%Z -> wr4 m9 prot 270 x = m8 x).
  { intros x Hx Hq. unfold wr4. rewrite MemSplit.wbytes_outside by (rewrite ?u_Z2bv by lia; zlen; lia).
    apply OUT9. lia. }
  assert (HEAP : forall (q : word) k (x : word), live A6 q = Some k -> (u q <= u x < u q + k)%Z -> wr4 m9 prot 270 x = m8 x).
  { intros q k x Lq Hx. destruct (blk_byte C A6 m8 _ q k x CK HW Lq Hx) as (_ & _ & _ & NW & _).
    assert (NW' : ~ (c_top C - LSTK <= u x < c_top C)%Z) by exact NW.
    apply KEEPh; lia. }
  assert (PX10 : PIXat (wr4 m9 prot 270) pixs (hdv w h 1 cm datas)).
  { pose proof PX as (Hp0 & Hp64 & _).
    apply (PIXat_frame m8 _ pixs _ PX). intros x Hx. apply (HEAP (Z_to_bv 64 pixs) 64%Z x); [rewrite E; exact Lp | rewrite u_Z2bv by lia; lia]. }
  assert (HCM10 : cm = 0%Z \/ (CMAPat (wr4 m9 prot 270) cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                                live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [HC | (HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right].
    refine (conj _ (conj HC2 (conj HC3 HC4))). pose proof HC1 as (Hc0 & Hc24 & _).
    apply (CMAPat_frame m8 _ cm cv HC1). intros x Hx. apply (HEAP (Z_to_bv 64 cm) 24%Z x); [rewrite E; exact HC3 | rewrite u_Z2bv by lia; lia]. }
  assert (OC10 : OCC (wr4 m9 prot 270) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m8 _ s); [lia | lia | | exact OC]. intros b n Hb Hn. destruct n as [|n]; [reflexivity|].
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply KEEPh; lia. }
  apply (oc_after_q3 fr cs C A A6 (wr4 m9 prot 270) md vm6 r13 regs s pixs w h cm datas cv ret f0 f1 (wr4 Mr prot 270) S kR bR
           CK HW10 FZ E PM10 Hs16 Hlo Hhi Hret H2 ltac:(oca_g) ltac:(rewrite N1; reflexivity) ltac:(oca_g) N10 N11
           PX10 HOK Hw Hh Lp Ld HCM10 OC10
           ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                 destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; oca_g)
           ROOM HkR HbR K).
Qed.

Lemma oc_arm_c0 : forall fr cs C A A6 (m8 Mr : word -> option byte) md vm6 rS regs (s pixs prot w h cm datas : Z) (cv : cmapv)
    (ret f0 f1 : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A6 m8 (with_vmmaps vm6 md) -> frm_zero cs -> (forall q, live A6 q = live A q) -> POSTM C A s Mr m8 -> W C A Mr md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  (s <= prot)%Z -> (prot + 4 <= c_top C)%Z -> (prot mod 4 = 0)%Z ->
  getr rS 2 = Z_to_bv 64 (s - 96) -> getr rS 4 = Z_to_bv 64 0x1381d0 -> getr rS 8 = Z_to_bv 64 pixs -> getr rS 9 = Z_to_bv 64 prot ->
  getr rS 10 = Z_to_bv 64 3 ->
  PIXat m8 pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m8 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m8 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rS x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s (wr4 Mr prot 0) m' -> oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) rS (0xaf740 : word) m8 al_rom) (with_vmmaps vm6 md)) S.
Proof.
  intros fr cs C A A6 m8 Mr md vm6 rS regs s pixs prot w h cm datas cv ret f0 f1 S kR bR
    CK HW FZ E PM HWr Hs16 Hlo Hhi Hret H2 Hp1 Hp2 Hp4 R2 R4 R8 R9 R10 PX HOK Hw Hh Lp Ld HCM OC KEEP ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  destruct (oc_K0a al_rom (mkFP fr cs) rS m8 R10) as (r11 & RUN11 & M1' & M10' & M11' & AG11).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN11 |].
  apply (lept_stderr1P8_W (fx := mkFP fr cs) C A6 m8 (with_vmmaps vm6 md) r11 (s - 96) 0x113ab 0x1055c 57 16 (Z_to_bv 64 0xaf75c) S CK HW
           ltac:(oca_g) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
           M1' ltac:(red; apply bv_eq; reflexivity) M10' M11' ltac:(oca_kc; cbn; tauto) str_oc_f0 str_oc_proc).
  intros m9 r12 HW9 OUT9 GR9 CS12. unfold LSF in OUT9.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => let v := eval vm_compute in (bv_unsigned pc) in
    replace pc with (@BV 64 v I : word) by (apply bv_eq; reflexivity) end.
  destruct (oc_K0b al_rom (mkFP fr cs) r12 m9 prot pixs ltac:(lia) ltac:(lia) Hp4
              (W_sok_win C A6 m9 _ prot 4 CK HW9 ltac:(lia) ltac:(cbn; lia)) ltac:(oca_g) ltac:(oca_g))
    as (r13 & RUN13 & N1 & N10 & N11 & AG13).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN13 |].
  assert (HW10 : W C A6 (wr4 m9 prot 0) (with_vmmaps vm6 md)).
  { unfold wr4. apply W_store_win; [exact CK | exact HW9 | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (PM9 : POSTM C A s Mr m9).
  { eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A6 _ _ _ SUB).
    apply (POSTM_range C A6 m8 _ m9 (s - 96 - 3376) (s - 96) s CK HW OUT9); lia. }
  assert (PM10 : POSTM C A s (wr4 Mr prot 0) (wr4 m9 prot 0)).
  { unfold wr4. apply (POSTM_wr_both C A md s Mr m9 (Z_to_bv 64 prot) _ CK HWr PM9); [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (KEEPh : forall x : word, ~ (s - 96 - 3376 <= u x < s - 96)%Z -> ~ (prot <= u x < prot + 4)%Z -> wr4 m9 prot 0 x = m8 x).
  { intros x Hx Hq. unfold wr4. rewrite MemSplit.wbytes_outside by (rewrite ?u_Z2bv by lia; zlen; lia).
    apply OUT9. lia. }
  assert (HEAP : forall (q : word) k (x : word), live A6 q = Some k -> (u q <= u x < u q + k)%Z -> wr4 m9 prot 0 x = m8 x).
  { intros q k x Lq Hx. destruct (blk_byte C A6 m8 _ q k x CK HW Lq Hx) as (_ & _ & _ & NW & _).
    assert (NW' : ~ (c_top C - LSTK <= u x < c_top C)%Z) by exact NW.
    apply KEEPh; lia. }
  assert (PX10 : PIXat (wr4 m9 prot 0) pixs (hdv w h 1 cm datas)).
  { pose proof PX as (Hp0 & Hp64 & _).
    apply (PIXat_frame m8 _ pixs _ PX). intros x Hx. apply (HEAP (Z_to_bv 64 pixs) 64%Z x); [rewrite E; exact Lp | rewrite u_Z2bv by lia; lia]. }
  assert (HCM10 : cm = 0%Z \/ (CMAPat (wr4 m9 prot 0) cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                                live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [HC | (HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right].
    refine (conj _ (conj HC2 (conj HC3 HC4))). pose proof HC1 as (Hc0 & Hc24 & _).
    apply (CMAPat_frame m8 _ cm cv HC1). intros x Hx. apply (HEAP (Z_to_bv 64 cm) 24%Z x); [rewrite E; exact HC3 | rewrite u_Z2bv by lia; lia]. }
  assert (OC10 : OCC (wr4 m9 prot 0) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m8 _ s); [lia | lia | | exact OC]. intros b n Hb Hn. destruct n as [|n]; [reflexivity|].
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply KEEPh; lia. }
  apply (oc_after_copy fr cs C A A6 (wr4 m9 prot 0) md vm6 r13 regs s pixs w h cm datas cv ret f0 f1 (wr4 Mr prot 0) S kR bR
           CK HW10 FZ E PM10 Hs16 Hlo Hhi Hret H2 ltac:(oca_g) ltac:(rewrite N1; reflexivity) ltac:(oca_g) N10 N11
           PX10 HOK Hw Hh Lp Ld HCM10 OC10
           ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                 destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; oca_g)
           ROOM HkR HbR K).
Qed.

Lemma oc_arm_c1 : forall fr cs C A A6 (m8 Mr : word -> option byte) md vm6 rS regs (s pixs prot w h cm datas : Z) (cv : cmapv)
    (ret f0 f1 : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A6 m8 (with_vmmaps vm6 md) -> frm_zero cs -> (forall q, live A6 q = live A q) -> POSTM C A s Mr m8 -> W C A Mr md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  (s <= prot)%Z -> (prot + 4 <= c_top C)%Z -> (prot mod 4 = 0)%Z ->
  getr rS 2 = Z_to_bv 64 (s - 96) -> getr rS 4 = Z_to_bv 64 0x1381d0 -> getr rS 8 = Z_to_bv 64 pixs -> getr rS 9 = Z_to_bv 64 prot ->
  getr rS 10 = Z_to_bv 64 3 ->
  PIXat m8 pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m8 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m8 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rS x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s (wr4 Mr prot 0) m' -> oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) rS (0xaf81c : word) m8 al_rom) (with_vmmaps vm6 md)) S.
Proof.
  intros fr cs C A A6 m8 Mr md vm6 rS regs s pixs prot w h cm datas cv ret f0 f1 S kR bR
    CK HW FZ E PM HWr Hs16 Hlo Hhi Hret H2 Hp1 Hp2 Hp4 R2 R4 R8 R9 R10 PX HOK Hw Hh Lp Ld HCM OC KEEP ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  destruct (oc_K1a al_rom (mkFP fr cs) rS m8 R10) as (r11 & RUN11 & M1' & M10' & M11' & AG11).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN11 |].
  apply (lept_stderr1P8_W (fx := mkFP fr cs) C A6 m8 (with_vmmaps vm6 md) r11 (s - 96) 0x128e8 0x1055c 45 16 (Z_to_bv 64 0xaf838) S CK HW
           ltac:(oca_g) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
           M1' ltac:(red; apply bv_eq; reflexivity) M10' M11' ltac:(oca_kc; cbn; tauto) str_oc_f1 str_oc_proc).
  intros m9 r12 HW9 OUT9 GR9 CS12. unfold LSF in OUT9.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => let v := eval vm_compute in (bv_unsigned pc) in
    replace pc with (@BV 64 v I : word) by (apply bv_eq; reflexivity) end.
  destruct (oc_K01b al_rom (mkFP fr cs) r12 m9 prot pixs ltac:(lia) ltac:(lia) Hp4
              (W_sok_win C A6 m9 _ prot 4 CK HW9 ltac:(lia) ltac:(cbn; lia)) ltac:(oca_g) ltac:(oca_g))
    as (r13 & RUN13 & N1 & N10 & N11 & AG13).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN13 |].
  assert (HW10 : W C A6 (wr4 m9 prot 0) (with_vmmaps vm6 md)).
  { unfold wr4. apply W_store_win; [exact CK | exact HW9 | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (PM9 : POSTM C A s Mr m9).
  { eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A6 _ _ _ SUB).
    apply (POSTM_range C A6 m8 _ m9 (s - 96 - 3376) (s - 96) s CK HW OUT9); lia. }
  assert (PM10 : POSTM C A s (wr4 Mr prot 0) (wr4 m9 prot 0)).
  { unfold wr4. apply (POSTM_wr_both C A md s Mr m9 (Z_to_bv 64 prot) _ CK HWr PM9); [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (KEEPh : forall x : word, ~ (s - 96 - 3376 <= u x < s - 96)%Z -> ~ (prot <= u x < prot + 4)%Z -> wr4 m9 prot 0 x = m8 x).
  { intros x Hx Hq. unfold wr4. rewrite MemSplit.wbytes_outside by (rewrite ?u_Z2bv by lia; zlen; lia).
    apply OUT9. lia. }
  assert (HEAP : forall (q : word) k (x : word), live A6 q = Some k -> (u q <= u x < u q + k)%Z -> wr4 m9 prot 0 x = m8 x).
  { intros q k x Lq Hx. destruct (blk_byte C A6 m8 _ q k x CK HW Lq Hx) as (_ & _ & _ & NW & _).
    assert (NW' : ~ (c_top C - LSTK <= u x < c_top C)%Z) by exact NW.
    apply KEEPh; lia. }
  assert (PX10 : PIXat (wr4 m9 prot 0) pixs (hdv w h 1 cm datas)).
  { pose proof PX as (Hp0 & Hp64 & _).
    apply (PIXat_frame m8 _ pixs _ PX). intros x Hx. apply (HEAP (Z_to_bv 64 pixs) 64%Z x); [rewrite E; exact Lp | rewrite u_Z2bv by lia; lia]. }
  assert (HCM10 : cm = 0%Z \/ (CMAPat (wr4 m9 prot 0) cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                                live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [HC | (HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right].
    refine (conj _ (conj HC2 (conj HC3 HC4))). pose proof HC1 as (Hc0 & Hc24 & _).
    apply (CMAPat_frame m8 _ cm cv HC1). intros x Hx. apply (HEAP (Z_to_bv 64 cm) 24%Z x); [rewrite E; exact HC3 | rewrite u_Z2bv by lia; lia]. }
  assert (OC10 : OCC (wr4 m9 prot 0) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m8 _ s); [lia | lia | | exact OC]. intros b n Hb Hn. destruct n as [|n]; [reflexivity|].
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply KEEPh; lia. }
  apply (oc_after_copy fr cs C A A6 (wr4 m9 prot 0) md vm6 r13 regs s pixs w h cm datas cv ret f0 f1 (wr4 Mr prot 0) S kR bR
           CK HW10 FZ E PM10 Hs16 Hlo Hhi Hret H2 ltac:(oca_g) ltac:(rewrite N1; reflexivity) ltac:(oca_g) N10 N11
           PX10 HOK Hw Hh Lp Ld HCM10 OC10
           ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                 destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; oca_g)
           ROOM HkR HbR K).
Qed.


Lemma oct_m4 : forall s k : Z, (s mod 16 = 0)%Z -> (k mod 4 = 0)%Z -> ((s - k) mod 4 = 0)%Z.
Proof.
  intros s k Hs Hk. apply Z.mod_divide in Hs; [|lia]. apply Z.mod_divide in Hk; [|lia]. apply Z.mod_divide; [lia|].
  destruct Hs as [a Ha]. destruct Hk as [b Hb]. exists (4 * a - b)%Z. lia.
Qed.

Lemma oct_livk_at : forall A (M M' : word -> option byte) (p k : Z) (x : word), LIVK A M M' ->
  live A (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= 2 ^ 64)%Z -> (p <= u x < p + k)%Z -> M' x = M x.
Proof.
  intros A M M' p k x L Lp H0 H1 Hx. pose proof (u64_range x) as Ux.
  pose proof (L (Z_to_bv 64 p) k (u x - p)%Z Lp ltac:(lia)) as EQ.
  unfold at_ in EQ. rewrite u_Z2bv in EQ by lia. replace (p + (u x - p))%Z with (u x) in EQ by lia.
  assert (EX : Z_to_bv 64 (u x) = x) by (apply bv_eq; rewrite u_Z2bv by lia; reflexivity).
  rewrite EX in EQ. exact EQ.
Qed.

Ltac oct_pc := lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => let v := eval vm_compute in (bv_unsigned pc) in
  replace pc with (@BV 64 v I : word) by (apply bv_eq; reflexivity) end.

Lemma oc_tail_W : forall fr6 cs6 C A A6 (m m6 : word -> option byte) md vm6 regs r8 (s pixs pup plf prot w h cm datas y0 y1 : Z) (cv : cmapv)
    (ret f0 f1 : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md -> W C A6 m6 (with_vmmaps vm6 md) -> frm_zero cs6 -> (forall q, live A6 q = live A q) -> POSTM C A s m m6 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 3680 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  getr regs 4 = Z_to_bv 64 0x1381d0 ->
  (s <= pup)%Z -> (pup + 4 <= c_top C)%Z -> (s <= plf)%Z -> (plf + 4 <= c_top C)%Z -> (s <= prot)%Z -> (prot + 4 <= c_top C)%Z ->
  (pup + 4 <= plf \/ plf + 4 <= pup)%Z -> (pup + 4 <= prot \/ prot + 4 <= pup)%Z -> (plf + 4 <= prot \/ prot + 4 <= plf)%Z ->
  (pup mod 4 = 0)%Z -> (plf mod 4 = 0)%Z -> (prot mod 4 = 0)%Z ->
  PIXat m pixs (hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  OCC m6 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1 ->
  rdn SEGS m6 (Z_to_bv 64 (s - 72)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 y0)) ->
  rdn SEGS m6 (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 y1)) ->
  getr r8 2 = Z_to_bv 64 (s - 96) -> getr r8 4 = Z_to_bv 64 0x1381d0 -> getr r8 8 = Z_to_bv 64 pixs -> getr r8 9 = Z_to_bv 64 prot ->
  getr r8 18 = Z_to_bv 64 0 -> getr r8 19 = Z_to_bv 64 plf -> getr r8 20 = Z_to_bv 64 pup ->
  (forall x, In x [3; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r8 x = getr regs x) ->
  aroom A6 vm6 (kR + (RK_pixcopy + 3)) (bR + RB_oc_arm w h cm) -> (0 <= kR)%Z -> (0 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs' (M : word -> option byte), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     (M = m \/ exists y0 y1 y2 : Z, M = wr4 (wr4 (wr4 m pup y0) plf y1) prot y2) -> POSTM C A s M m' ->
     oc_res C A A' m' regs' cv -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr6 cs6) r8 (0xaf66c : word) m6 al_rom) (with_vmmaps vm6 md)) S.
Proof using P16 PINS.
  intros fr6 cs6 C A A6 m m6 md vm6 regs r8 s pixs pup plf prot w h cm datas y0 y1 cv ret f0 f1 S kR bR
    CK HW0 HW6 FZ E PM6 Hs16 Hlo Hhi Hret H2 H4 Hu1 Hu2 Hl1 Hl2 Hp1 Hp2 Dul Dup Dlp Mu Ml Mp PX HOK Hw Hh Lp Ld HCM OC Y0 Y1
    R2 R4 R8 R9 R18 R19 R20 KEEP8 ROOM HkR HbR K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (SUB : sub_live A A6) by (intros q k Hq; rewrite E; exact Hq).
  set (b0 := word_to_le_bytes 4 (Z_to_bv 64 y0)) in *. set (b1 := word_to_le_bytes 4 (Z_to_bv 64 y1)) in *.
  assert (Lb0 : length b0 = 4%nat) by (unfold b0; rewrite length_N_to_le_bytes; reflexivity).
  assert (Lb1 : length b1 = 4%nat) by (unfold b1; rewrite length_N_to_le_bytes; reflexivity).
  destruct (oc_E al_rom fr6 cs6 r8 m6 s pup plf 0 b0 b1 ltac:(lia) ltac:(lia) Hu1 ltac:(lia) Hl1 ltac:(lia) Mu Ml Dul Y0 Lb0 Y1 Lb1
              (W_sok_win C A6 m6 _ pup 4 CK HW6 ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A6 m6 _ plf 4 CK HW6 ltac:(lia) ltac:(cbn; lia))
              R2 R18 R19 R20)
    as (fr7 & r7 & RUN7 & Q1 & Q10 & Q11 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
  set (m7 := O23LeptOcSegs.OCW m6 pup plf b0 b1) in *.
  assert (HW7 : W C A6 m7 (with_vmmaps vm6 md)).
  { unfold m7, O23LeptOcSegs.OCW. apply W_store_win; [exact CK | | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; rewrite Lb1; cbn; lia].
    apply W_store_win; [exact CK | exact HW6 | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; rewrite Lb0; cbn; lia]. }
  set (Mr := wr4 (wr4 m pup y0) plf y1).
  assert (HWr1 : W C A (wr4 m pup y0) md).
  { unfold wr4. apply W_store_win; [exact CK | exact HW0 | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (HWr : W C A Mr md).
  { unfold Mr. unfold wr4 at 1. apply W_store_win; [exact CK | exact HWr1 | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  assert (PM7 : POSTM C A s Mr m7).
  { unfold Mr, m7, O23LeptOcSegs.OCW. unfold wr4 at 1.
    apply (POSTM_wr_both C A md s (wr4 m pup y0) _ (Z_to_bv 64 plf) _ CK HWr1); [| rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia].
    unfold wr4. apply (POSTM_wr_both C A md s m m6 (Z_to_bv 64 pup) _ CK HW0 PM6); [rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; zlen; lia]. }
  oct_pc.
  apply (makeOrientDecision_W fr7 cs6 C A6 m7 (with_vmmaps vm6 md) r7 (s - 96) (s - 68) _ S CK HW7 FZ ltac:(oca_g)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold MOD_STACK, LSF; lia) ltac:(lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q10 Q11 ltac:(lia) ltac:(lia) (oct_m4 s 68 Hs16 eq_refl)).
  intros fr8 cs8 m8 r9 o HW8 FZ8 CS9 Ho PM8 V10_9.
  assert (PM8' : POSTM C A s Mr m8).
  { eapply POSTM_trans; [exact PM7 |].
    assert (WPw : W C A6 (wr4 m7 (s - 68) o) (with_vmmaps vm6 md) /\ POSTM C A6 s m7 (wr4 m7 (s - 68) o)) by (unfold wr4; wp_win CK).
    eapply POSTM_trans; [exact (POSTM_sub C A A6 _ _ _ SUB (proj2 WPw)) |].
    exact (POSTM_sub C A A6 _ _ _ SUB (POSTM_mono C A6 (s - 96) s _ _ ltac:(lia) PM8)). }
  assert (MD8 : rdn SEGS m8 (Z_to_bv 64 (s - 68)) 4 = Some (Z_to_le_bytes 4 o)).
  { rewrite <- p16_segs. rewrite (FRM_rdn_above C (s - 96) (wr4 m7 (s - 68) o) m8 (s - 68) 4 CK (proj1 PM8)) by (cbn; lia).
    rewrite p16_segs. unfold wr4. rewrite <- (w2b_Z 4 o) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv; lia. }
  assert (OUTr : forall x : word, ~ (c_top C - LSTK <= u x < c_top C)%Z -> Mr x = m x).
  { intros x Hx. unfold Mr, wr4. rewrite !MemSplit.wbytes_outside by (rewrite ?u_Z2bv by lia; zlen; lia). reflexivity. }
  assert (HEAPr : forall (q : word) k (x : word), live A q = Some k -> (u q <= u x < u q + k)%Z -> Mr x = m x).
  { intros q k x Lq Hx. destruct (blk_byte C A m md q k x CK HW0 Lq Hx) as (_ & _ & _ & NW & _).
    assert (NW' : ~ (c_top C - LSTK <= u x < c_top C)%Z) by exact NW. exact (OUTr x NW'). }
  assert (PX8 : PIXat m8 pixs (hdv w h 1 cm datas)).
  { pose proof PX as (Hp0 & Hp64 & _).
    assert (PXr : PIXat Mr pixs (hdv w h 1 cm datas))
      by (apply (PIXat_frame m _ pixs _ PX); intros x Hx; apply (HEAPr (Z_to_bv 64 pixs) 64%Z x Lp); rewrite u_Z2bv by lia; lia).
    apply (PIXat_frame Mr m8 pixs _ PXr). intros x Hx. exact (oct_livk_at A Mr m8 pixs 64 x (proj2 PM8') Lp ltac:(lia) ltac:(lia) Hx). }
  assert (HCM8 : cm = 0%Z \/ (CMAPat m8 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                               live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [HC | (HC1 & HC2 & HC3 & HC4)]; [left; exact HC | right].
    refine (conj _ (conj HC2 (conj HC3 HC4))). pose proof HC1 as (Hc0 & Hc24 & _).
    assert (CMr : CMAPat Mr cm cv)
      by (apply (CMAPat_frame m _ cm cv HC1); intros x Hx; apply (HEAPr (Z_to_bv 64 cm) 24%Z x HC3); rewrite u_Z2bv by lia; lia).
    apply (CMAPat_frame Mr m8 cm cv CMr). intros x Hx. exact (oct_livk_at A Mr m8 cm 24 x (proj2 PM8') HC3 ltac:(lia) ltac:(lia) Hx). }
  assert (OC8 : OCC m8 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) f0 f1).
  { apply (OCC_pw m6 m8 s); [lia | lia | | exact OC]. intros b n Hb Hn. destruct n as [|n]; [reflexivity|].
    rewrite <- p16_segs. rewrite (FRM_rdn_above C (s - 96) (wr4 m7 (s - 68) o) m8 b (Datatypes.S n) CK (proj1 PM8)) by lia.
    rewrite p16_segs. unfold wr4, m7, O23LeptOcSegs.OCW.
    rewrite !rdn_wbytes_out_Z by (rewrite ?Lb0, ?Lb1; zlen; lia). reflexivity. }
  assert (KEEPS : forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r9 x = getr r8 x).
  { intros x Hx; cbn [In] in Hx; destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; oca_g. }
  assert (Oc : o = 0%Z \/ o = 1%Z \/ o = 2%Z \/ o = 3%Z \/ o = 4%Z) by lia.
  destruct Oc as [-> | [-> | [-> | [-> | ->]]]].
  - pose proof jt_oc0 as JK.
    lazymatch type of JK with rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
      pose proof (W_rdn_ro C A6 m8 _ a 4 HW8 ltac:(cbn; lia) ltac:(cbn; lia)) as RO end.
    rewrite p16_segs in RO. rewrite <- RO in JK.
    lazymatch type of JK with _ = Some (Z_to_le_bytes 4 ?e) =>
    destruct (oc_S al_rom (mkFP fr8 cs8) r9 m8 s 0 e ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(red; apply bv_eq; reflexivity)
                (V23LeptBase.W_sev_got _ _ _ _ HW8) (V23LeptBase.W_sev _ _ _ _ HW8) MD8 JK ltac:(oca_g))
      as (r10 & RUN10 & S10 & AG10) end.
    oct_pc.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN10 |].
    oct_pc.
    apply (oc_arm_c0 fr8 cs8 C A A6 m8 Mr md vm6 r10 regs s pixs prot w h cm datas cv ret f0 f1 S kR bR CK HW8 FZ8 E PM8' HWr Hs16 Hlo Hhi Hret H2
             Hp1 Hp2 Mp ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) S10 PX8 HOK Hw Hh Lp Ld HCM8 OC8
             ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                   destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
                   match goal with |- getr _ ?y = _ => rewrite (AG10 y ltac:(notin_lit)), (KEEPS y ltac:(cbn; tauto)) end;
                   first [apply KEEP8; cbn; tauto | rewrite R4, H4; reflexivity])
             ROOM HkR HbR
             (fun fr' cs' A' m' vm' regs' HWx FZx CSx PMx RESx ROOMx =>
                K fr' cs' A' m' vm' regs' (wr4 Mr prot 0) HWx FZx CSx
                  (or_intror (ex_intro _ y0 (ex_intro _ y1 (ex_intro _ 0%Z eq_refl)))) PMx RESx ROOMx)).
  - pose proof jt_oc1 as JK.
    lazymatch type of JK with rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
      pose proof (W_rdn_ro C A6 m8 _ a 4 HW8 ltac:(cbn; lia) ltac:(cbn; lia)) as RO end.
    rewrite p16_segs in RO. rewrite <- RO in JK.
    lazymatch type of JK with _ = Some (Z_to_le_bytes 4 ?e) =>
    destruct (oc_S al_rom (mkFP fr8 cs8) r9 m8 s 1 e ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(red; apply bv_eq; reflexivity)
                (V23LeptBase.W_sev_got _ _ _ _ HW8) (V23LeptBase.W_sev _ _ _ _ HW8) MD8 JK ltac:(oca_g))
      as (r10 & RUN10 & S10 & AG10) end.
    oct_pc.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN10 |].
    oct_pc.
    apply (oc_arm_c1 fr8 cs8 C A A6 m8 Mr md vm6 r10 regs s pixs prot w h cm datas cv ret f0 f1 S kR bR CK HW8 FZ8 E PM8' HWr Hs16 Hlo Hhi Hret H2
             Hp1 Hp2 Mp ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) S10 PX8 HOK Hw Hh Lp Ld HCM8 OC8
             ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                   destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
                   match goal with |- getr _ ?y = _ => rewrite (AG10 y ltac:(notin_lit)), (KEEPS y ltac:(cbn; tauto)) end;
                   first [apply KEEP8; cbn; tauto | rewrite R4, H4; reflexivity])
             ROOM HkR HbR
             (fun fr' cs' A' m' vm' regs' HWx FZx CSx PMx RESx ROOMx =>
                K fr' cs' A' m' vm' regs' (wr4 Mr prot 0) HWx FZx CSx
                  (or_intror (ex_intro _ y0 (ex_intro _ y1 (ex_intro _ 0%Z eq_refl)))) PMx RESx ROOMx)).
  - pose proof jt_oc2 as JK.
    lazymatch type of JK with rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
      pose proof (W_rdn_ro C A6 m8 _ a 4 HW8 ltac:(cbn; lia) ltac:(cbn; lia)) as RO end.
    rewrite p16_segs in RO. rewrite <- RO in JK.
    lazymatch type of JK with _ = Some (Z_to_le_bytes 4 ?e) =>
    destruct (oc_S al_rom (mkFP fr8 cs8) r9 m8 s 2 e ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(red; apply bv_eq; reflexivity)
                (V23LeptBase.W_sev_got _ _ _ _ HW8) (V23LeptBase.W_sev _ _ _ _ HW8) MD8 JK ltac:(oca_g))
      as (r10 & RUN10 & S10 & AG10) end.
    oct_pc.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN10 |].
    oct_pc.
    apply (oc_arm_q1 fr8 cs8 C A A6 m8 Mr md vm6 r10 regs s pixs prot w h cm datas cv ret f0 f1 S kR bR CK HW8 FZ8 E PM8' HWr Hs16 Hlo Hhi Hret H2
             Hp1 Hp2 Mp ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) S10 PX8 HOK Hw Hh Lp Ld HCM8 OC8
             ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                   destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
                   match goal with |- getr _ ?y = _ => rewrite (AG10 y ltac:(notin_lit)), (KEEPS y ltac:(cbn; tauto)) end;
                   first [apply KEEP8; cbn; tauto | rewrite R4, H4; reflexivity])
             ROOM HkR HbR
             (fun fr' cs' A' m' vm' regs' HWx FZx CSx PMx RESx ROOMx =>
                K fr' cs' A' m' vm' regs' (wr4 Mr prot 90) HWx FZx CSx
                  (or_intror (ex_intro _ y0 (ex_intro _ y1 (ex_intro _ 90%Z eq_refl)))) PMx RESx ROOMx)).
  - pose proof jt_oc3 as JK.
    lazymatch type of JK with rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
      pose proof (W_rdn_ro C A6 m8 _ a 4 HW8 ltac:(cbn; lia) ltac:(cbn; lia)) as RO end.
    rewrite p16_segs in RO. rewrite <- RO in JK.
    lazymatch type of JK with _ = Some (Z_to_le_bytes 4 ?e) =>
    destruct (oc_S al_rom (mkFP fr8 cs8) r9 m8 s 3 e ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(red; apply bv_eq; reflexivity)
                (V23LeptBase.W_sev_got _ _ _ _ HW8) (V23LeptBase.W_sev _ _ _ _ HW8) MD8 JK ltac:(oca_g))
      as (r10 & RUN10 & S10 & AG10) end.
    oct_pc.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN10 |].
    oct_pc.
    apply (oc_arm_q2 fr8 cs8 C A A6 m8 Mr md vm6 r10 regs s pixs prot w h cm datas cv ret f0 f1 S kR bR CK HW8 FZ8 E PM8' HWr Hs16 Hlo Hhi Hret H2
             Hp1 Hp2 Mp ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) S10 PX8 HOK Hw Hh Lp Ld HCM8 OC8
             ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                   destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
                   match goal with |- getr _ ?y = _ => rewrite (AG10 y ltac:(notin_lit)), (KEEPS y ltac:(cbn; tauto)) end;
                   first [apply KEEP8; cbn; tauto | rewrite R4, H4; reflexivity])
             ROOM HkR HbR
             (fun fr' cs' A' m' vm' regs' HWx FZx CSx PMx RESx ROOMx =>
                K fr' cs' A' m' vm' regs' (wr4 Mr prot 180) HWx FZx CSx
                  (or_intror (ex_intro _ y0 (ex_intro _ y1 (ex_intro _ 180%Z eq_refl)))) PMx RESx ROOMx)).
  - pose proof jt_oc4 as JK.
    lazymatch type of JK with rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
      pose proof (W_rdn_ro C A6 m8 _ a 4 HW8 ltac:(cbn; lia) ltac:(cbn; lia)) as RO end.
    rewrite p16_segs in RO. rewrite <- RO in JK.
    lazymatch type of JK with _ = Some (Z_to_le_bytes 4 ?e) =>
    destruct (oc_S al_rom (mkFP fr8 cs8) r9 m8 s 4 e ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(red; apply bv_eq; reflexivity)
                (V23LeptBase.W_sev_got _ _ _ _ HW8) (V23LeptBase.W_sev _ _ _ _ HW8) MD8 JK ltac:(oca_g))
      as (r10 & RUN10 & S10 & AG10) end.
    oct_pc.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN10 |].
    oct_pc.
    apply (oc_arm_q3 fr8 cs8 C A A6 m8 Mr md vm6 r10 regs s pixs prot w h cm datas cv ret f0 f1 S kR bR CK HW8 FZ8 E PM8' HWr Hs16 Hlo Hhi Hret H2
             Hp1 Hp2 Mp ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) ltac:(oca_g) S10 PX8 HOK Hw Hh Lp Ld HCM8 OC8
             ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                   destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
                   match goal with |- getr _ ?y = _ => rewrite (AG10 y ltac:(notin_lit)), (KEEPS y ltac:(cbn; tauto)) end;
                   first [apply KEEP8; cbn; tauto | rewrite R4, H4; reflexivity])
             ROOM HkR HbR
             (fun fr' cs' A' m' vm' regs' HWx FZx CSx PMx RESx ROOMx =>
                K fr' cs' A' m' vm' regs' (wr4 Mr prot 270) HWx FZx CSx
                  (or_intror (ex_intro _ y0 (ex_intro _ y1 (ex_intro _ 270%Z eq_refl)))) PMx RESx ROOMx)).
Qed.

Lemma FRM_winO : forall C s' (m m' : word -> option byte) (x : word), Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z ->
  (s' <= u x < c_top C)%Z -> m' x = m x.
Proof.
  intros C s' m m' x CK F Hlo Hx.
  assert (WN : win C x) by (unfold win; lia).
  destruct (win_facts C x CK WN) as (_ & Hat & Hg & He & Hh & _ & _).
  apply F; [exact (above_not_gap C x Hat) | exact Hg | exact He | exact Hh | unfold scratch; lia].
Qed.

Ltac ocf_rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac ocf_pc RUN :=
  match type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ => replace g with pc by (csr; apply bv_eq; reflexivity) end end.
Ltac ocf_wsz := rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac ocf_zl := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Theorem pixOrientCorrect_W : pixOrientCorrect_contract (OC_STACK UDD_STK) (RK_oc RK_udd) (RB_oc RB_udd).
Proof using RB_udd_le1 RB_udd_nn RK_udd_nn H_udd P16 PINS.
  pose proof H_udd as HU. unfold pixUpDownDetect_contract in HU.
  intros fr cs C A m md regs s pixs pup plf prot w h d cm datas cv ret S CK HW FZ MB H2 Hs16 Hlo Hhi H1 Hret H4
    H10 H11 H12 H13 H14 Hu1 Hu2 Hu3 Hl1 Hl2 Hl3 Hr1 Hr2 Hr3 D1 D2 D3 PX HOK Hw Hh LP LD LP0 LD0 CMX kR bR AR HkR HbR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  pose proof (u64_range (c_sp0 C)) as SP.
  assert (SB : (c_top C - LSTK + 96 + 3680 <= s)%Z) by (unfold OC_STACK in Hlo; lia).
  assert (SBu : (c_top C - LSTK + UDD_STK <= s - 96)%Z) by (unfold OC_STACK in Hlo; lia).
  assert (M96 : ((s - 96) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (S4 : (s mod 4 = 0)%Z).
  { pose proof (Z.div_mod s 16 ltac:(lia)) as E. rewrite Hs16, Z.add_0_r in E. rewrite E.
    replace (16 * (s / 16))%Z with ((4 * (s / 16)) * 4)%Z by ring. apply Z.mod_mul. lia. }
  assert (S8 : (s mod 8 = 0)%Z).
  { pose proof (Z.div_mod s 16 ltac:(lia)) as E. rewrite Hs16, Z.add_0_r in E. rewrite E.
    replace (16 * (s / 16))%Z with ((2 * (s / 16)) * 8)%Z by ring. apply Z.mod_mul. lia. }
  pose proof (aroom_nonneg A (m_vmmaps md) kR bR AR) as [Nk Nb].
  assert (KP : RK_pix = 2%Z) by reflexivity. assert (KC : RK_cmapcopy = 2%Z) by reflexivity.
  assert (KPC : RK_pixcopy = 4%Z) by reflexivity.
  assert (EK : RK_oc RK_udd = (2 * RK_udd + (RK_pix + RK_cmapcopy) + (RK_pixcopy + 3))%Z) by reflexivity.
  assert (EB : RB_oc RB_udd w h cm = (RB_udd w h cm + (RB_pixT (4 * (wpl_of h 1 * w)) + RB_cmapcopy) + RB_udd h w 1 + RB_oc_arm w h cm)%Z)
    by reflexivity.
  assert (NBA : (RB_pixT (4 * (wpl_of h 1 * w)) + RB_cmapcopy <= RB_oc_arm w h cm)%Z) by (unfold RB_oc_arm; lia).
  pose proof (RB_pixT_nonneg (4 * (wpl_of h 1 * w))) as NBT.
  assert (NBC : RB_cmapcopy = 262144%Z) by reflexivity.
  pose proof (RB_udd_nn w h cm) as NB1. pose proof (RB_udd_nn h w 1) as NB2. pose proof RK_udd_nn as NK.
  assert (FRD : forall Ax (mx my : word -> option byte) (s' : Z), POSTM C Ax s' mx my -> (c_top C - LSTK <= s')%Z ->
                forall (b : Z) (n : nat), (s' <= b)%Z -> (b + Z.of_nat n <= c_top C)%Z ->
                rdn SEGS my (Z_to_bv 64 b) n = rdn SEGS mx (Z_to_bv 64 b) n).
  { intros Ax mx my s' PMx Hs' b n X1 X2. apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply (FRM_winO C s' mx my x CK (proj1 PMx)); lia. }
  pose proof (ai_live_hull A m (m_vmmaps md) (Z_to_bv 64 pixs) 64 (w_inv _ _ _ _ HW) LP) as (_ & AL16 & _).
  pose proof PX as (Pp0 & Pp64 & _).
  rewrite u_Z2bv in AL16 by lia.
  assert (P8 : (pixs mod 8 = 0)%Z) by (pose proof (mod16_plus_mod8 pixs 0 AL16 eq_refl) as E; rewrite Z.add_0_r in E; exact E).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW LP ltac:(lia)) as [BP1 BP2].
  rewrite u_Z2bv in BP1, BP2 by lia.
  pose proof HOK as (DV & _).
  assert (Dr : (0 <= d < 2 ^ 31)%Z) by (unfold dval in DV; lia).
  assert (KEEPS : forall Ax (mx : word -> option byte), sub_live A Ax -> LIVK A m mx ->
     PIXat mx pixs (hdv w h d cm datas) /\
     (cm = 0%Z \/ (CMAPat mx cm cv /\ cmap_ok cv /\ live Ax (Z_to_bv 64 cm) = Some 24%Z /\
                  live Ax (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                  live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None))).
  { intros Ax mx SBx LK. split.
    - apply (PIXat_frame m mx pixs _ PX). intros x Hx.
      exact (O23LeptCmap2.LIVK_at A m mx pixs 64 x LK LP ltac:(lia) ltac:(lia) Hx).
    - destruct CMX as [-> | (CM & CO & LC & LA & LC0 & LA0)]; [left; reflexivity | right].
      pose proof CM as (C0 & C24 & _).
      split; [| split; [exact CO | split; [exact (SBx _ _ LC) | split; [exact (SBx _ _ LA) | split; assumption]]]].
      apply (CMAPat_frame m mx cm cv CM). intros x Hx.
      exact (O23LeptCmap2.LIVK_at A m mx cm 24 x LK LC ltac:(lia) ltac:(lia) Hx). }
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true) by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | ocf_zl]).
  destruct (oc_P al_rom fr cs regs m s pixs pup plf prot 0 d ret FZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Dr P8
              (PIX_rd_d SEGS m pixs _ PX) SOKf H2 H1 H10 H11 H12 H13 H14)
    as (fr1 & r1 & RUN1 & R1_2 & R1_10 & R1_8 & R1_9 & R1_18 & R1_19 & R1_20 & AG1).
  ocf_pc RUN1. ocf_rzs HW RUN1.
  assert (WF : W C A (O23LeptOcSegs.OCF m s ret regs fr) md /\ POSTM C A s m (O23LeptOcSegs.OCF m s ret regs fr)).
  { unfold O23LeptOcSegs.OCF.
    repeat (apply (WP_win C A A); [exact CK | | apply sub_live_refl | ocf_wsz | ocf_wsz | lia]).
    split; [exact HW | apply POSTM_refl]. }
  destruct WF as [W0 PM0].
  pose proof (OCC_OCF m s ret regs fr ltac:(lia) ltac:(lia)) as OC0.
  destruct (Z.eq_dec d 1) as [-> | Hd1].
  2:{
    pose proof OC0 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    destruct (oc_Ab al_rom fr1 cs r1 (O23LeptOcSegs.OCF m s ret regs fr) s d ret (getr regs 8) (getr regs 9) (getr regs 18)
                (getr regs 19) (getr regs 20) (reg_get fr 8) (reg_get fr 9) ltac:(lia) ltac:(lia) Dr Hd1
                (W_sev_got C A _ md W0) (W_sev C A _ md W0) Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 R1_2 R1_10)
      as (fr2 & r2 & RUN2 & R2_2 & R2_1 & R2_10 & R2_11 & R2_12 & R2_8 & R2_9 & R2_18 & R2_19 & R2_20 & AG2).
    ocf_pc RUN2. ocf_rzs W0 RUN2.
    apply (returnErrorPtr_W (fx := mkFP fr2 cs) C A _ md r2 s _ _ _ _ ret (Z_to_bv 64 0) S CK W0 R2_2 Hs16
             ltac:(cbv [V23LeptBase.LSF]; lia) Hhi R2_1 Hret R2_10 R2_11 R2_12 str_oc_err str_oc_proc).
    intros m' r' W' FR' MG' CS' RV'.
    pose proof (HK fr2 cs A m' (m_vmmaps md) r' m) as HK'. rewrite with_vmmaps_same in HK'.
    apply HK'.
    + exact W'.
    + exact FZ.
    + apply cs_kept_intro; csr; reflexivity.
    + left; reflexivity.
    + apply (POSTM_trans _ _ _ _ _ _ PM0).
      apply (POSTM_range C A _ md m' _ s s CK W0 FR'); cbv [V23LeptBase.LSF]; lia.
    + left. split; [exact RV' | intros q; reflexivity].
    + apply (aroom_mono A (m_vmmaps md) kR bR); [exact AR | lia | lia]. }
  destruct (oc_A al_rom (mkFP fr1 cs) r1 (O23LeptOcSegs.OCF m s ret regs fr) s pixs 0 ltac:(lia) ltac:(lia) R1_2 R1_10 R1_8 R1_18)
    as (r2 & RUN2 & R2_1 & R2_10 & R2_11 & R2_12 & R2_13 & R2_14 & AG2).
  ocf_pc RUN2. ocf_rzs W0 RUN2.
  destruct (KEEPS A _ (sub_live_refl A) (proj2 PM0)) as [PX0 CM0].
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ =>
    replace g with (Z_to_bv 64 PC_UDD) by (apply bv_eq; reflexivity) end.
  apply (HU fr1 cs C A (O23LeptOcSegs.OCF m s ret regs fr) md r2 (s - 96)%Z pixs (s - 72)%Z w h cm datas cv (getr r2 1) S
           CK W0 FZ MB ltac:(csr; reflexivity) M96 SBu ltac:(lia) eq_refl ltac:(rewrite R2_1; apply ret_ok_even; reflexivity)
           ltac:(csr; reflexivity) R2_10 R2_11 R2_12 R2_13 R2_14 ltac:(lia) ltac:(lia)
           ltac:(rewrite <- Zminus_mod_idemp_l, S4; reflexivity)
           (or_intror (conj PX0 (conj HOK (conj Hw (conj Hh (conj LP (conj LD (conj LP0 (conj LD0 CM0)))))))))
           kR bR AR ltac:(lia) ltac:(lia)).
  intros fr3 cs3 A1 m1 vm1 r3 y1 W1 FZ3 CS3 PS1 LV1 AR1.
  assert (PW1 : POSTM C A s (O23LeptOcSegs.OCF m s ret regs fr) (O23LeptSelGP.wr4 (O23LeptOcSegs.OCF m s ret regs fr) (s - 72) y1)).
  { unfold O23LeptSelGP.wr4. apply (POSTM_wbytes_win C A _ md _ _ s CK W0); ocf_wsz. }
  pose proof (POSTM_trans _ _ _ _ _ _ PM0 (POSTM_trans _ _ _ _ _ _ PW1 (POSTM_mono C A (s - 96) s _ _ ltac:(lia) PS1))) as PM1.
  destruct (oc_B al_rom (mkFP fr3 cs3) r3 m1 pixs ltac:(csr; reflexivity)) as (r4 & RUN4 & R4_1 & R4_10 & R4_11 & AG4).
  ocf_pc RUN4. ocf_rzs W1 RUN4.
  destruct (KEEPS A1 m1 (sub_live_eq A A1 LV1) (proj2 PM1)) as [PX1 CM1].
  apply (pixRotate90_W (fx := mkFP fr3 cs3) C A1 m1 (with_vmmaps vm1 md) r4 (s - 96) pixs 1 w h cm datas 1 cv (getr r4 1) S
           CK W1 ltac:(csr; reflexivity) M96 ltac:(cbv [R90_STACK V23LeptBase.LSF]; lia) ltac:(lia) eq_refl
           ltac:(rewrite R4_1; apply ret_ok_even; reflexivity) ltac:(csr; reflexivity) R4_10 R4_11 (or_introl eq_refl)
           PX1 HOK Hw Hh ltac:(rewrite LV1; exact LP) ltac:(rewrite LV1; exact LD)
           ltac:(destruct CM1 as [E | (Q1 & Q2 & Q3 & Q4 & _)]; [left; exact E | right; exact (conj Q1 (conj Q2 (conj Q3 Q4)))])
           (kR - RK_udd) (bR - RB_udd w h cm) ltac:(rewrite with_vmmaps_vmmaps; exact AR1) ltac:(lia) ltac:(lia)).
  intros A2 m2 vm2 r5 W2 CS5 PS2 RES2 AR2.
  rewrite with_vmmaps_twice in W2 |- *.
  pose proof (POSTM_trans _ _ _ _ _ _ PM1 (POSTM_mono C A (s - 96) s _ _ ltac:(lia) (POSTM_sub C A A1 (s - 96) _ _ (sub_live_eq A A1 LV1) PS2)))
    as PM2.
  assert (SUB2 : sub_live A A2).
  { destruct RES2 as [[_ LQ] | (p1 & cd & dt & _ & PT)].
    - intros q k Hq. rewrite LQ, LV1. exact Hq.
    - destruct PT as (_ & _ & _ & _ & _ & _ & _ & N1 & N2 & _ & _ & _ & _ & _ & CR).
      intros q k Hq. rewrite <- LV1 in Hq.
      destruct (bv_eq_dec _ q (Z_to_bv 64 p1)) as [-> | Q1]; [congruence |].
      destruct (bv_eq_dec _ q (Z_to_bv 64 dt)) as [-> | Q2]; [congruence |].
      destruct CR as [(_ & LQ) | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2 & _ & _ & _ & _ & _ & LQ)].
      + rewrite (LQ q Q1 Q2). exact Hq.
      + destruct (bv_eq_dec _ q (Z_to_bv 64 cd)) as [-> | Q3]; [congruence |].
        destruct (bv_eq_dec _ q (Z_to_bv 64 ad)) as [-> | Q4]; [congruence |].
        rewrite (LQ q Q1 Q2 Q3 Q4). exact Hq. }
  assert (WPC : W C A2 (O23LeptOcSegs.OCP m2 s (getr r5 10)) (with_vmmaps vm2 md) /\
                POSTM C A2 s m2 (O23LeptOcSegs.OCP m2 s (getr r5 10))).
  { unfold O23LeptOcSegs.OCP.
    apply (WP_win C A2 A2 m2 m2 _ _ _ s CK (conj W2 (POSTM_refl C A2 s m2)) (sub_live_refl A2)); ocf_wsz. }
  destruct WPC as [WC PMC].
  assert (U2 : exists pp1 cm2 dt2 cv2, getr r5 10 = Z_to_bv 64 pp1 /\
             udd_src C A2 (O23LeptOcSegs.OCP m2 s (getr r5 10)) pp1 h w cm2 dt2 cv2 /\ (RB_udd h w cm2 <= RB_udd h w 1)%Z).
  { destruct RES2 as [[E5 _] | (p1 & cd & dt & E5 & PT)].
    - exists 0%Z, 1%Z, 0%Z, cv. split; [exact E5 | split; [left; reflexivity | lia]].
    - destruct PT as (P1a & P1b & _ & _ & _ & _ & _ & _ & _ & Z1 & Z2 & L1 & L2 & PXd & CR).
      pose proof (proj2 PMC) as LKC.
      assert (PXc : PIXat (O23LeptOcSegs.OCP m2 s (getr r5 10)) p1 (hdv h w 1 cd dt)).
      { apply (PIXat_frame m2 _ p1 _ PXd). intros x Hx.
        exact (O23LeptCmap2.LIVK_at A2 m2 _ p1 64 x LKC L1 ltac:(lia) ltac:(lia) Hx). }
      pose proof (O23LeptOcW.hdr_ok_rot w h HOK Hw Hh) as HOKr.
      destruct CR as [(-> & _) | (ad & CO & _ & _ & A4 & _ & _ & _ & _ & _ & _ & _ & _ & Z3 & Z4 & L3 & L4 & CMd & _)].
      + exists p1, 0%Z, dt, cv. split; [exact E5 |]. split; [| apply RB_udd_le1].
        right. exact (conj PXc (conj HOKr (conj Hh (conj Hw (conj L1 (conj L2 (conj Z1 (conj Z2 (or_introl eq_refl))))))))).
      + exists p1, cd, dt, (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0). split; [exact E5 |]. split; [| apply RB_udd_le1].
        right. split; [exact PXc |]. split; [exact HOKr |]. split; [exact Hh |]. split; [exact Hw |].
        split; [exact L1 |]. split; [exact L2 |]. split; [exact Z1 |]. split; [exact Z2 |]. right.
        pose proof CMd as (C0 & C24 & _).
        split; [| split; [| split; [exact L3 | split; [exact L4 | split; [exact Z3 | exact Z4]]]]].
        * apply (CMAPat_frame m2 _ cd _ CMd). intros x Hx.
          exact (O23LeptCmap2.LIVK_at A2 m2 _ cd 24 x LKC L3 ltac:(lia) ltac:(lia) Hx).
        * destruct CO as (CO1 & CO2 & CO3 & CO4). unfold cmap_ok. cbn [c_d c_nalloc c_n c_arr].
          split; [exact CO1 | split; [exact CO2 | split; [exact CO3 | lia]]]. }
  destruct U2 as (pp1 & cm2 & dt2 & cv2 & E5 & US & RBle).
  destruct (oc_C al_rom (mkFP fr3 cs3) r5 m2 s 0 ltac:(lia) ltac:(lia) (W_sok_win C A2 m2 _ (s - 88) 8 CK W2 ltac:(lia) ltac:(ocf_zl))
              ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r6 & RUN6 & R6_1 & R6_10 & R6_11 & R6_12 & R6_13 & R6_14 & AG6).
  ocf_pc RUN6. ocf_rzs W2 RUN6.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ =>
    replace g with (Z_to_bv 64 PC_UDD) by (apply bv_eq; reflexivity) end.
  apply (HU fr3 cs3 C A2 (O23LeptOcSegs.OCP m2 s (getr r5 10)) (with_vmmaps vm2 md) r6 (s - 96)%Z pp1 (s - 76)%Z h w cm2 dt2 cv2 (getr r6 1) S
           CK WC FZ3 MB ltac:(csr; reflexivity) M96 SBu ltac:(lia) eq_refl ltac:(rewrite R6_1; apply ret_ok_even; reflexivity)
           ltac:(csr; reflexivity) ltac:(rewrite R6_10; exact E5) R6_11 R6_12 R6_13 R6_14 ltac:(lia) ltac:(lia)
           ltac:(rewrite <- Zminus_mod_idemp_l, S4; reflexivity) US
           (kR - RK_udd - RK_pix - RK_cmapcopy)%Z (bR - RB_udd w h cm - RB_pixT (4 * (wpl_of h 1 * w)) - RB_cmapcopy)%Z
           ltac:(rewrite with_vmmaps_vmmaps; exact AR2) ltac:(lia) ltac:(lia)).
  intros fr4 cs4 A3 m3 vm3 r7 y2 W3 FZ4 CS7 PS3 LV3 AR3.
  rewrite with_vmmaps_twice in W3 |- *.
  destruct (oc_D al_rom (mkFP fr4 cs4) r7 m3 s ltac:(lia) ltac:(lia) ltac:(csr; reflexivity)) as (r8 & RUN8 & R8_1 & R8_10 & AG8).
  ocf_pc RUN8. ocf_rzs W3 RUN8.
  assert (PW2 : POSTM C A2 s (O23LeptOcSegs.OCP m2 s (getr r5 10)) (O23LeptSelGP.wr4 (O23LeptOcSegs.OCP m2 s (getr r5 10)) (s - 76) y2)).
  { unfold O23LeptSelGP.wr4. apply (POSTM_wbytes_win C A2 _ _ _ _ s CK WC); ocf_wsz. }
  pose proof (POSTM_trans _ _ _ _ _ _ PMC (POSTM_trans _ _ _ _ _ _ PW2 (POSTM_mono C A2 (s - 96) s _ _ ltac:(lia) PS3))) as PM3a.
  pose proof (POSTM_trans _ _ _ _ _ _ PM2 (POSTM_sub C A A2 s _ _ SUB2 PM3a)) as PM3.
  assert (SUB3 : sub_live A A3) by (intros q k Hq; rewrite LV3; exact (SUB2 q k Hq)).
  assert (CH : forall (b : Z) (n : nat), (s - 72 <= b)%Z -> (b + Z.of_nat n <= s)%Z ->
               rdn SEGS m3 (Z_to_bv 64 b) n = rdn SEGS (O23LeptSelGP.wr4 (O23LeptOcSegs.OCF m s ret regs fr) (s - 72) y1) (Z_to_bv 64 b) n).
  { intros b n X1 X2.
    rewrite (FRD _ _ _ _ PS3) by lia. unfold O23LeptSelGP.wr4 at 1.
    rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; ocf_zl).
    unfold O23LeptOcSegs.OCP. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; ocf_zl).
    rewrite (FRD _ _ _ _ PS2) by lia. rewrite (FRD _ _ _ _ PS1) by lia. reflexivity. }
  assert (RY1 : rdn SEGS m3 (Z_to_bv 64 (s - 72)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 y1))).
  { rewrite CH by ocf_zl. unfold O23LeptSelGP.wr4. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (RY2 : rdn SEGS m3 (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 y2))).
  { rewrite (FRD _ _ _ _ PS3) by ocf_zl. unfold O23LeptSelGP.wr4. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (OC3 : forall (b : Z) (n : nat), (s - 64 <= b)%Z -> (b + Z.of_nat n <= s)%Z ->
                rdn SEGS m3 (Z_to_bv 64 b) n = rdn SEGS (O23LeptOcSegs.OCF m s ret regs fr) (Z_to_bv 64 b) n).
  { intros b n X1 X2. rewrite CH by lia. unfold O23LeptSelGP.wr4. apply rdn_wbytes_out_Z.
    rewrite length_N_to_le_bytes; ocf_zl. }
  assert (TAIL : forall A4 (m4 : word -> option byte) vm4 r9 (k4 b4 : Z),
     W C A4 m4 (with_vmmaps vm4 md) -> (forall q, live A4 q = live A q) -> POSTM C A s m m4 ->
     (forall (b : Z) (n : nat), (s - 80 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m4 (Z_to_bv 64 b) n = rdn SEGS m3 (Z_to_bv 64 b) n) ->
     cs_kept r8 r9 -> aroom A4 vm4 k4 b4 ->
     (kR - RK_oc RK_udd + (RK_pixcopy + 3) <= k4)%Z -> (bR - RB_oc RB_udd w h cm + RB_oc_arm w h cm <= b4)%Z ->
     realizes SEGS (mkCfg (@mkst (mkFP fr4 cs4) r9 (getr r8 1) m4 al_rom) (with_vmmaps vm4 md)) S).
  { intros A4 m4 vm4 r9 k4 b4 W4 LV4 PM4 K4 CS9 AR4 Hk4 Hb4.
    assert (OCC4 : OCC m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (reg_get fr 8) (reg_get fr 9)).
    { apply (OCC_pw (O23LeptOcSegs.OCF m s ret regs fr)); [lia | lia | | exact OC0].
      intros b n X1 X2. rewrite K4 by lia. exact (OC3 b n X1 X2). }
    assert (RY1' : rdn SEGS m4 (Z_to_bv 64 (s - 72)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 y1))) by (rewrite K4 by ocf_zl; exact RY1).
    assert (RY2' : rdn SEGS m4 (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 y2))) by (rewrite K4 by ocf_zl; exact RY2).
    assert (AR4' : aroom A4 vm4 (kR - RK_oc RK_udd + (RK_pixcopy + 3)) (bR - RB_oc RB_udd w h cm + RB_oc_arm w h cm))
      by (apply (aroom_mono A4 vm4 k4 b4); [exact AR4 | lia | lia]).
    replace (getr r8 1) with (0xaf66c : word) by (rewrite R8_1; apply bv_eq; reflexivity).
    apply (oc_tail_W fr4 cs4 C A A4 m m4 md vm4 regs r9 s pixs pup plf prot w h cm datas y1 y2 cv ret (reg_get fr 8) (reg_get fr 9) S
             (kR - RK_oc RK_udd) (bR - RB_oc RB_udd w h cm)
             CK HW W4 FZ4 LV4 PM4 Hs16 SB Hhi Hret H2 H4 Hu1 Hu2 Hl1 Hl2 Hr1 Hr2 D1 D2 D3 Hu3 Hl3 Hr3 PX HOK Hw Hh LP LD
             ltac:(destruct CMX as [E | (Q1 & Q2 & Q3 & Q4 & _)]; [left; exact E | right; exact (conj Q1 (conj Q2 (conj Q3 Q4)))])
             OCC4 RY1' RY2'
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             ltac:(intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<- | Hx]; [csr; reflexivity |]); destruct Hx)
             AR4' ltac:(lia) ltac:(lia) HK). }
  destruct RES2 as [[E5' LQ2] | (p1 & cd & dt & E5' & PT)].
  - assert (RZ : rdn SEGS m3 (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 0)).
    { rewrite (FRD _ _ _ _ PS3) by ocf_zl. unfold O23LeptSelGP.wr4.
      rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; ocf_zl). unfold O23LeptOcSegs.OCP.
      rewrite OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia).
      rewrite E5', w2b_Z by lia. reflexivity. }
    apply (pixDestroy_null_W (fx := mkFP fr4 cs4) C A3 m3 (with_vmmaps vm3 md) r8 (s - 96) (s - 88) None (getr r8 1) S
             CK W3 ltac:(csr; reflexivity) M96 ltac:(lia) ltac:(lia) eq_refl ltac:(rewrite R8_1; apply ret_ok_even; reflexivity)
             R8_10 ltac:(cbv [slotok]; lia) ltac:(rewrite <- Zminus_mod_idemp_l, S8; reflexivity) RZ).
    intros m4 r9 W4 CS9 PM4' K4'.
    apply (TAIL A3 m4 vm3 r9 (kR - RK_udd - RK_pix - RK_cmapcopy - RK_udd)%Z
             (bR - RB_udd w h cm - RB_pixT (4 * (wpl_of h 1 * w)) - RB_cmapcopy - RB_udd h w cm2)%Z W4).
    + intros q. rewrite LV3, LQ2, LV1. reflexivity.
    + exact (POSTM_trans _ _ _ _ _ _ PM3 (POSTM_mono C A (s - 96) s _ _ ltac:(lia) (POSTM_sub C A A3 (s - 96) _ _ SUB3 PM4'))).
    + intros b n X1 X2. apply (FRD _ _ _ _ PM4'); lia.
    + exact CS9.
    + exact AR3.
    + lia.
    + lia.
  - destruct PT as (P1a & P1b & P1m & D1a & D1b & D1m & NEpd & N1 & N2 & Z1 & Z2 & L1 & L2 & PXd & CR).
    pose proof (proj2 PM3a) as LK23.
    assert (PX3 : PIXat m3 p1 (hdv h w 1 cd dt)).
    { apply (PIXat_frame m2 m3 p1 _ PXd). intros x Hx. exact (O23LeptCmap2.LIVK_at A2 m2 m3 p1 64 x LK23 L1 ltac:(lia) ltac:(lia) Hx). }
    assert (RP : rdn SEGS m3 (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 p1)).
    { rewrite (FRD _ _ _ _ PS3) by ocf_zl. unfold O23LeptSelGP.wr4.
      rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; ocf_zl). unfold O23LeptOcSegs.OCP.
      rewrite OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia).
      rewrite E5', w2b_Z by lia. reflexivity. }
    assert (Rpos : (0 < 4 * (wpl_of h 1 * w))%Z) by (pose proof (O23LeptOcW.wpl1_pos h Hh); nia).
    pose proof (aroom_nonneg _ _ _ _ AR3) as [N3k N3b].
    destruct CR as [(-> & LQ) | (ad & CO & Cd1 & Cd2 & Ad1 & Ad2 & NE1 & NE2 & NE3 & NE4 & NE5 & N3 & N4 & Z3 & Z4 & L3 & L4 & CMd & LQ)].
    + refine (pixDestroy_keep_W (fx := mkFP fr4 cs4) C A3 m3 (with_vmmaps vm3 md) r8 (s - 96) (s - 88) p1 0 0 (4 * (wpl_of h 1 * w))
                (hdv h w 1 0 dt) cv (getr r8 1) S
                CK W3 ltac:(csr; reflexivity) M96 ltac:(cbv [ALLOC_STACK]; lia) ltac:(lia) ltac:(lia) eq_refl
                ltac:(rewrite R8_1; apply ret_ok_even; reflexivity) ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, S8; reflexivity)
                R8_10 RP PX3 eq_refl eq_refl eq_refl ltac:(rewrite LV3; exact L1) Z1 ltac:(rewrite LV3; exact L2) Z2 Rpos ltac:(cbn; lia)
                (or_introl eq_refl) _).
      intros A4 m4 vm4 r9 W4 CS9 PD PM4' RZ4 KB4 RT4.
      rewrite with_vmmaps_twice in W4 |- *. rewrite with_vmmaps_vmmaps in RT4.
      change (p_data (hdv h w 1 0 dt)) with dt in PD.
      assert (LV4 : forall q, live A4 q = live A q).
      { intros q. destruct PD as (PD1 & PD2 & _ & PD4).
        destruct (bv_eq_dec _ q (Z_to_bv 64 p1)) as [-> | Q1]; [rewrite PD1, <- LV1; exact (eq_sym N1) |].
        destruct (bv_eq_dec _ q (Z_to_bv 64 dt)) as [-> | Q2]; [rewrite (PD2 ltac:(lia)), <- LV1; exact (eq_sym N2) |].
        rewrite PD4; [rewrite LV3, (LQ q Q1 Q2), LV1; reflexivity | exact Q1 | intros _; exact Q2 | intros C0; exfalso; apply C0; reflexivity]. }
      pose proof (RT4 _ _ AR3 ltac:(lia) ltac:(lia)) as AR4.
      eapply (TAIL A4 m4 vm4 r9 _ _ W4 LV4).
      * exact (POSTM_trans _ _ _ _ _ _ PM3 (POSTM_mono C A (s - 88 + 8) s _ _ ltac:(lia) (POSTM_sub C A A4 _ _ _ (sub_live_eq A A4 LV4) PM4'))).
      * intros b n X1 X2. apply (FRD _ _ _ _ PM4'); lia.
      * exact CS9.
      * exact AR4.
      * lia.
      * lia.
    + assert (CMK : CMAPat m3 cd (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0)).
      { pose proof CMd as (C0 & C24 & _). apply (CMAPat_frame m2 m3 cd _ CMd). intros x Hx.
        exact (O23LeptCmap2.LIVK_at A2 m2 m3 cd 24 x LK23 L3 ltac:(lia) ltac:(lia) Hx). }
      refine (pixDestroy_keep_W (fx := mkFP fr4 cs4) C A3 m3 (with_vmmaps vm3 md) r8 (s - 96) (s - 88) p1 cd (4 * c_nalloc cv)
                (4 * (wpl_of h 1 * w)) (hdv h w 1 cd dt) (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) (getr r8 1) S
                CK W3 ltac:(csr; reflexivity) M96 ltac:(cbv [ALLOC_STACK]; lia) ltac:(lia) ltac:(lia) eq_refl
                ltac:(rewrite R8_1; apply ret_ok_even; reflexivity) ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, S8; reflexivity)
                R8_10 RP PX3 eq_refl eq_refl eq_refl ltac:(rewrite LV3; exact L1) Z1 ltac:(rewrite LV3; exact L2) Z2 Rpos ltac:(cbn; lia)
                _ _).
      { right. cbn [c_arr]. split; [exact CMK |]. split; [rewrite LV3; exact L3 |]. split; [rewrite LV3; exact L4 |].
        split; [exact Z3 |]. split; [exact Z4 |]. cbn. destruct CO as (_ & _ & CO3 & _). lia. }
      intros A4 m4 vm4 r9 W4 CS9 PD PM4' RZ4 KB4 RT4.
      rewrite with_vmmaps_twice in W4 |- *. rewrite with_vmmaps_vmmaps in RT4.
      change (p_data (hdv h w 1 cd dt)) with dt in PD. change (c_arr (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0)) with ad in PD.
      assert (LV4 : forall q, live A4 q = live A q).
      { intros q. destruct PD as (PD1 & PD2 & PD3 & PD4).
        destruct (PD3 ltac:(lia)) as [PD3a PD3b].
        destruct (bv_eq_dec _ q (Z_to_bv 64 p1)) as [-> | Q1]; [rewrite PD1, <- LV1; exact (eq_sym N1) |].
        destruct (bv_eq_dec _ q (Z_to_bv 64 dt)) as [-> | Q2]; [rewrite (PD2 ltac:(lia)), <- LV1; exact (eq_sym N2) |].
        destruct (bv_eq_dec _ q (Z_to_bv 64 cd)) as [-> | Q3]; [rewrite PD3a, <- LV1; exact (eq_sym N3) |].
        destruct (bv_eq_dec _ q (Z_to_bv 64 ad)) as [-> | Q4]; [rewrite PD3b, <- LV1; exact (eq_sym N4) |].
        rewrite PD4; [rewrite LV3, (LQ q Q1 Q2 Q3 Q4), LV1; reflexivity | exact Q1 | intros _; exact Q2 | intros _; split; assumption]. }
      pose proof (RT4 _ _ AR3 ltac:(lia) ltac:(lia)) as AR4.
      eapply (TAIL A4 m4 vm4 r9 _ _ W4 LV4).
      * exact (POSTM_trans _ _ _ _ _ _ PM3 (POSTM_mono C A (s - 88 + 8) s _ _ ltac:(lia) (POSTM_sub C A A4 _ _ _ (sub_live_eq A A4 LV4) PM4'))).
      * intros b n X1 X2. apply (FRD _ _ _ _ PM4'); lia.
      * exact CS9.
      * exact AR4.
      * lia.
      * lia.
Qed.

End OcW.
