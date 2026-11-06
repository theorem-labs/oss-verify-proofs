(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem. 
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OSSVerify.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.ct.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import RT_iface2 LibKitA ARun BnHeapA.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApUTacB.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApATac ApBImg ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeKit TimeKit2 TimeKit3 TimeFmtPure TimeToTmDefs TimeToTmFeb W_time_to_tm_it.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeB Require Import TimeDefsA TimeKitA W_time_leavesA TimeToTmDefsA W_time_to_tm_itA W_time_to_tm_BA W_time_to_tm_CA.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import CtUbTabB CtUTacB.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtTimeB Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac rzstep := OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep.    (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Section WithRT.
Context {AR : ARun}.
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.

(* [comment removed for export] *)
Local Ltac iter_callA i m0 MU OFF ACCD ACCS ACCMIN ACCMAX :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let IT := fresh "IT" in
    pose proof (t2t_iterA i ltac:(lia)) as IT; unfold t2t_iterA_stmt in IT;
    eapply evt_cut;
    [ eapply IT; clear IT; try eassumption;
      first [ unfold t2t_lowA, MASK47, gcells, zb8; match goal with H : rw_cells _ mx _ _ |- _ => exact H end
            | eapply (acc_munch ctbsegs _ m0 mx); [ first [exact ACCD | exact ACCS | exact ACCMIN | exact ACCMAX] | exact MU | exact OFF | unfold A_MINTAB_A, A_MAXTAB_A; alia | unfold A_MINTAB_A, A_MAXTAB_A; alia ]
            | alia ]
    | clear IT; intros ms' PO; unfold t2t_iterA_post in PO; revert ms' PO; post_call ctbsegs mx;
      match goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => let v := eval vm_compute in p in change p with v end ]
  end.

(* [comment removed for export] *)
Local Ltac isdig_callA cv ESPA :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evt_cut;
    [ eapply (ossl_ascii_isdigit_specA _ _) with (c := cv); rewrite ?ESPA;
      [ eassumption | eassumption | eassumption | lia | lia | reflexivity ]
    | intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO; post_call ctbsegs mx; rewrite ?ESPA in * ]
  end.

(* [comment removed for export] *)
Definition t2t_finA_post (sp : word) (spa : Z) (gp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte)
    (f DA GS tm : Z) (t : tm6) (wd yd : Z) (j0 j160 j168 junk : list byte) (g : nat) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x24 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 (Z_to_bv 64 GS) sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
                  x18 x19 x20 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 1) x23 x24 (Z_to_bv 64 SHB) (Z_to_bv 64 f) (Z_to_bv 64 1) x28 x29 x30 x31)
             F (Z_to_bv 64 0x2747ec) fc None m' (seg_rom ctbsegs)
    /\ munch [(lo, spa + 200); (f + 32, f + 32 + 56)]%Z m m' /\ wmono ctbsegs m m' /\ mem_inv ctbsegs m' /\ stk ctbsegs m' lo spa
    /\ rw_cells ctbsegs m' spa (t2t_lowA j0 j160 j168 19 tm f DA GS (t_mon t - 1) (t_year t - 1900) g junk)
    /\ rw_cells ctbsegs m' (f + 32) (TM_CELLS_A (t_sec t) (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd).

Lemma t2t_segDA : forall (x1 sp gp x5 x6 x10 x11 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo spa f DA GS tm ms wd yd : Z) (t : tm6)
         (j0 j160 j168 junk : list byte) (g : nat),
  stk ctbsegs m lo spa -> mem_inv ctbsegs m -> ACEIL <= lo -> lo + 16 <= spa -> spa + 304 <= USTACK_TOP -> spa mod 16 = 0 ->
  SEGTOP_A <= ACEIL -> SHHI <= ACEIL -> ACEIL + STACK_WIN <= USTACK_TOP ->
  rw_cells ctbsegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> acc ctbsegs m DA 16 -> DA mod 8 = 0 ->
  0 < DA -> DA + 16 <= ACEIL ->
  rw_cells ctbsegs m GS (gcells t ms) -> acc ctbsegs m GS 19 -> GS mod 8 = 0 -> 0 < GS -> GS + 19 <= ACEIL ->
  rw_cells ctbsegs m spa (t2t_lowA j0 j160 j168 19 tm f DA GS (t_mon t - 1) (t_year t - 1900) g junk) ->
  acc ctbsegs m A_MINTAB_A 36 -> acc ctbsegs m A_MAXTAB_A 36 ->
  tm_valid t -> 0 <= ms < 1000 -> 0 <= f -> f + 128 <= ACEIL -> f mod 8 = 0 -> (f + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= f) ->
  (DA + 16 <= f + 32 \/ f + 32 + 56 <= DA) -> (GS + 19 <= f + 32 \/ f + 32 + 56 <= GS) -> 0 <= tm < 2^64 ->
  rw_cells ctbsegs m (f + 32) (TM_CELLS_A 0 0 0 (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd) ->
  evt ctbsegs (t2t_finA_post sp spa gp F fc lo m f DA GS tm t wd yd j0 j160 j168 junk g)
    (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 (Z_to_bv 64 GS) sp (Z_to_bv 64 spa) x10 x11 (Z_to_bv 64 4) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 8) (Z_to_bv 64 (f + 32)) x22 x23 x24 (Z_to_bv 64 SHB) (Z_to_bv 64 f) (Z_to_bv 64 1) x28 x29 x30 x31)
        F (Z_to_bv 64 T2T_HEAD_A) fc None m (seg_rom ctbsegs)).
Proof.
  intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX TV MSR F0 FHI F8 FG5 SEPD SEPS TMR TMP.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS).
  pose proof (munch_refl [(lo, spa + 200); (f + 32, f + 32 + 56)]%Z m) as MU. pose proof (wmono_refl ctbsegs m) as WM.
  assert (OFF : offshW [(lo, spa + 200); (f + 32, f + 32 + 56)]%Z) by (cbn [offshW]; alia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; lia).
  assert (SEPT : f + 32 + 56 <= spa - 16 \/ spa + 304 <= f + 32) by (clear - FHI CEILu LO; lia).
  unfold TM_CELLS_A in TMP. unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS. unfold CH_Z, CH_DOT in HS.
  (* [comment removed for export] *)
  iter_callA 4 m MU OFF ACCD ACCS ACCMIN ACCMAX. name_mem m1.
  change (fld 4 t) with (t_hour t) in *.
  step. step. zstep. step. step. brc.
  (* [comment removed for export] *)
  iter_callA 5 m MU OFF ACCD ACCS ACCMIN ACCMAX. name_mem m2.
  change (fld 5 t) with (t_min t) in *.
  step. step. zstep. step. step. brc.
  (* [comment removed for export] *)
  iter_callA 6 m MU OFF ACCD ACCS ACCMIN ACCMAX. name_mem m3.
  change (fld 6 t) with (t_sec t) in *.
  step. step. zstep. step. step. brc. step.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. rewrite (sx32_small 24) by lia. step. step. brc.
  (* [comment removed for export] *)
  step. try rewrite (zxb_lit 46) by lia. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc. step.
  pose proof (digit_range (ms / 100) ltac:(split; [apply Z.div_pos; lia| enough (ms / 100 < 10) by lia; apply Z.div_lt_upper_bound; lia])) as DG1.
  pose proof (digit_range ((ms / 10) mod 10) ltac:(pose proof (Z.mod_pos_bound (ms / 10) 10 ltac:(lia)); lia)) as DG2.
  pose proof (digit_range (ms mod 10) ltac:(pose proof (Z.mod_pos_bound ms 10 ltac:(lia)); lia)) as DG3.
  (* [comment removed for export] *)
  step. try rewrite (zxb_lit (digit (ms / 100))) by lia. step. isdig_callA (digit (ms / 100)) ESPA. rewrite (isdigit_range (digit (ms / 100))) by lia.
  step. brc. zstep. zstep. zstep. step. step. step. brc. step.
  (* [comment removed for export] *)
  step. try rewrite (zxb_lit (digit ((ms / 10) mod 10))) by lia. step. isdig_callA (digit ((ms / 10) mod 10)) ESPA. rewrite (isdigit_range (digit ((ms / 10) mod 10))) by lia.
  step. brc. zstep. zstep. zstep. step. step. step. brc. step.
  step. try rewrite (zxb_lit (digit (ms mod 10))) by lia. step. isdig_callA (digit (ms mod 10)) ESPA. rewrite (isdigit_range (digit (ms mod 10))) by lia.
  step. brc. zstep. zstep. zstep. step. step. step. brc. step.
  (* [comment removed for export] *)
  step. try rewrite (zxb_lit 90) by lia. step. isdig_callA 90 ESPA. rewrite (isdigit_false 90) by lia.
  step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc. step. step. step. brc. step.
  (* [comment removed for export] *)
  step. try rewrite (zxb_lit 90) by lia. step. step. brc. step. step. brc. step. step. brc.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. brc. step.
  name_mem m9. apply evt_done. unfold t2t_finA_post. do 20 eexists. exists m9. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [unfold t2t_lowA, MASK47; eassumption| unfold TM_CELLS_A; eassumption].
Qed.

End WithRT.
