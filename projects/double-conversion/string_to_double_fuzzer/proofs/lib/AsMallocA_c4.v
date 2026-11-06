(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsMallocA_base LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section L4.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[using="Type"] Lemma loop_4 : forall n regs M (u c FB : Z) (fl : Z -> Z),
  getr regs 13%bv = Z_to_bv 64 FB -> getr regs 12%bv = Z_to_bv 64 u -> getr regs 10%bv = Z_to_bv 64 c ->
  getr regs 14%bv = Z_to_bv 64 1023 ->
  0 <= u < 2 ^ 64 -> Z.of_nat n + 1 <= c <= 1024 -> 0x688000 <= FB -> FB + 1024 <= 0x800000000000 ->
  (forall j, 0 <= j < Z.of_nat n -> fl ((u + j) mod 1024) = 1) -> fl ((u + Z.of_nat n) mod 1024) = 0 ->
  (forall q, 0 <= q < 1024 -> cellN SEGS_A M (FB + q) 1 (fl q)) ->
  exists regs',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x5b568) M rom) (mkst regs' (Z_to_bv 64 0x5b5e0) M rom)
    /\ getr regs' 17%bv = Z_to_bv 64 ((u + Z.of_nat n) mod 1024)
    /\ getr regs' 15%bv = Z_to_bv 64 (FB + (u + Z.of_nat n) mod 1024)
    /\ getr regs' 12%bv = Z_to_bv 64 (u + Z.of_nat n)
    /\ keeps LOOP_KEEP regs regs'.
Proof.
  induction n as [|n IH]; intros regs M u c FB fl R13 R12 R10 R14 Hu Hc Hlo Hhi Hones Hzero Hcells.
  - (* [comment removed for export] *)
    cbn [Z.of_nat] in *. rewrite Z.add_0_r in *.
    pose proof (Hcells (u mod 1024) ltac:(lia)) as C0. rewrite Hzero in C0.
    zx_run SEGS_A constr:(lp_ctx 1024 10 1 0) 20%nat [0x5b568; 0x5b5e0] (SCR [] []) constr:(lp_pins 1023) [FB; u; c]
           constr:([Some (0x688000, 0x800000000000 - 1024); Some (0, 18446744073709551615); Some (1, 1024)]) regs M rom 0x5b568.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 C0; exact I) ltac:(exact I) ltac:(exact I).
    clear ZF. exists regs0. split; [exact ZM|].
    split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
    eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
  - (* [comment removed for export] *)
    pose proof (Hcells (u mod 1024) ltac:(lia)) as C0.
    rewrite <- (Z.add_0_r u) in C0 at 2. rewrite (Hones 0) in C0 by lia.
    zx_run SEGS_A constr:(lp_ctx 1024 10 2 1) 20%nat [0x5b568; 0x5b5e0] (SCR [] []) constr:(lp_pins 1023) [FB; u; c]
           constr:([Some (0x688000, 0x800000000000 - 1024); Some (0, 18446744073709551615); Some (2, 1024)]) regs M rom 0x5b568.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 C0; exact I) ltac:(exact I) ltac:(exact I).
    clear ZF.
    destruct (IH regs0 M ((u + 1) mod 2 ^ 64) (c - 1) FB fl) as (regs1 & MS & A7 & A5 & A2 & K).
    + zx_regv ZR.
    + etransitivity; [zx_regv ZR|]. apply Z2bv_eqm. rewrite Z.mod_mod by lia. reflexivity.
    + zx_regv ZR.
    + zx_regv ZR.
    + split; [apply Z.mod_pos_bound; lia|]. apply Z.mod_pos_bound. lia.
    + lia.
    + lia.
    + lia.
    + intros j Hj. etransitivity; [|apply (Hones (j + 1)); lia]. f_equal. lia.
    + etransitivity; [|exact Hzero]. f_equal. lia.
    + exact Hcells.
    + exists regs1. split; [eapply msteps_trans; [exact ZM | exact MS]|].
      split; [rewrite A7; f_equal; lia|]. split; [rewrite A5; f_equal; lia|].
      split; [rewrite A2; apply Z2bv_eqm; lia|].
      eapply keeps_trans; [|exact K]. eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
Qed.
End L4.

Lemma fs_consts_4 : fs_N 4 = 1024 /\ fs_flo 4 = 34816 /\ fs_fro 4 = 4231168 /\ fs_fsz 4 = 1024 /\ MALLOC_A 4 = 0x5b4d4.
Proof. repeat split; reflexivity. Qed.
Theorem malloc_4 : malloc_stmt 4.
Proof.
  unfold malloc_stmt.
  intros fx regs mem rom ret sp FS fl R1 Hret R2 Hsp16 Hsplo Hsphi Hdsp R4 Hrt Hro Hctx Htls Hfs4096 Hfslo Hfsapp Hfshi Dfs   (* [comment removed for export] *)
         Hdfs Hdsh Hlog Hgc Hfl Hex.
  pose proof fs_consts_4 as (EN & EFLO & EFRO & EFSZ & EENTRY).
  unfold fs_flag, fs_frame, fs_hint in *. rewrite EN, EFLO, EFRO, EFSZ, EENTRY in *. clear EN EFLO EFRO EFSZ EENTRY.
  unfold app_mem in Hfsapp. unfold KHI_A, HIEND_A, IMGHI_A, LOSH_A, MALLOC_FR, FS_LEN, FS_SHLO, FS_SHHI, FSTLS_A, TP_A, sh, SH_A, w64 in *.
  replace (Z_to_bv 5 2) with (2%bv : reg) in R2 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 4) with (4%bv : reg) in R4 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 10) with (10%bv : reg) by (apply bv_eq; reflexivity).
  pose proof (ret_ok_of_mod4 ret Hret) as Hret'.
  destruct Hctx as (CTXp & THR & DT & Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Bc1 & Bc2 & Bt1 & Bd1 & Ac & At & Ad).
  unfold ctx_cell_ok in Ac, At, Ad. unfold app_mem in Ac, At, Ad. unfold KHI_A, HIEND_A, IMGHI_A, LOSH_A, FS_LEN, TP_A in Hc5, Bc2, Ac, At, Ad.
  (* [comment removed for export] *)
  destruct Ac as (Ac1 & _ & _ & Ac2 & Ac3 & _). destruct At as (At1 & _ & _ & At2 & At3 & _). destruct Ad as (Ad1 & _ & _ & Ad2 & Ad3 & _).
  (* [comment removed for export] *)
  pose proof (icells_intro mem Hrt Hro) as IC. pose proof (mcells_intro mem Hrt Hro) as MC.
  assert (Cctx : cellN SEGS_A mem 0x6877e0 8 CTXp) by exact Hc1.
  assert (Cthr : cellN SEGS_A mem (CTXp + 0x98) 8 THR) by (apply cellN_u64'; [exact Hc2|lia|lia|lia]).
  destruct (cellN_ex_of_def SEGS_A mem (THR + 48) 8) as (t30 & Ct30 & _); [eapply mem_def_sub; [exact Hc3|lia|cbn; lia] | lia | cbn; lia |].
  destruct (cellN_ex_of_def SEGS_A mem (THR + 56) 8) as (t38 & Ct38 & _); [eapply mem_def_sub; [exact Hc3|lia|cbn; lia] | lia | cbn; lia |].
  assert (Cdt : cellN SEGS_A mem 0x666330 8 DT) by exact Hc4.
  assert (Cdt18 : cellN SEGS_A mem (DT + 24) 8 0x666328) by (apply cellN_u64'; [exact Hc5|lia|lia|lia]).
  assert (Ctls : cellN SEGS_A mem 0x666328 8 FS) by exact Htls.
  assert (Clog : cellN SEGS_A mem (FS + 88) 8 20) by (apply cellN_u64'; [exact Hlog|lia|lia|lia]).
  assert (Cgc : cellN SEGS_A mem (FS + 96) 1 0) by (apply cellN_byte; [exact Hgc|lia|lia|lia]).
  destruct (cellN_ex_of_def SEGS_A mem (FS + 32) 8) as (h & Ch & Rh); [eapply mem_def_sub; [exact Hdfs|lia|cbn; lia] | lia | cbn; lia |].
  change (2 ^ (8 * Z.of_nat 8)) with 18446744073709551616 in Rh.
  assert (Cfl : forall q, 0 <= q < 1024 -> cellN SEGS_A mem (FS + 34816 + q) 1 (fl q)).
  { intros q Hq. destruct (Hfl q Hq) as [Hb H01]. apply cellN_byte; [exact Hb|lia|lia|lia]. }
  clear Hc1 Hc2 Hc3 Hc4 Hc5 Htls Hlog Hgc Hrt Hro.
  hide Dfs; hide Ac3; hide At3; hide Ad3; hide Hsp16; hide Hfs4096; hide Hret.
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(p0_ctx) 20%nat [0x609b0] (SCR [] []) [(2%bv : reg, ZV 32)] [sp]
         constr:([Some (0x10007fff8000 + 256, 0x800000000000)]) regs mem rom 0x5b4d4.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kwd Hdsp; exact I) ltac:(exact I).
  clear ZF. rename regs0 into regsA. rename ZM into MA. rename ZR into RA. rename ZE into EA.
  match type of MA with msteps _ _ (mkst _ _ ?M _) => set (M0 := M) in * end.
  pose proof (u64_range (getr regs (Z_to_bv 5 1))) as Rr1. pose proof (u64_range (getr regs (Z_to_bv 5 8))) as Rr8.
  pose proof (u64_range (getr regs (Z_to_bv 5 9))) as Rr9. pose proof (u64_range (getr regs (Z_to_bv 5 18))) as Rr18.
  assert (U0 : unch mem M0 [(sp - 32, sp)]) by (clear - Hsplo Hsphi; subst M0; unchx).
  assert (G0 : mem_grows mem M0) by (clear - Hsplo Hsphi; subst M0; growsx).
  assert (S01 : cellN SEGS_A M0 (sp - 8) 8 (bv_unsigned (getr regs (Z_to_bv 5 1)))) by (clear - Hsplo Hsphi Rr1; subst M0; cellN_go).
  assert (S02 : cellN SEGS_A M0 (sp - 16) 8 (bv_unsigned (getr regs (Z_to_bv 5 8)))) by (clear - Hsplo Hsphi Rr8; subst M0; cellN_go).
  assert (S03 : cellN SEGS_A M0 (sp - 24) 8 (bv_unsigned (getr regs (Z_to_bv 5 9)))) by (clear - Hsplo Hsphi Rr9; subst M0; cellN_go).
  assert (S04 : cellN SEGS_A M0 (sp - 32) 8 (bv_unsigned (getr regs (Z_to_bv 5 18)))) by (clear - Hsplo Hsphi Rr18; subst M0; cellN_go).
  clearbody M0.
  (* [comment removed for export] *)
  destruct (icall rom regsA M0 (sp - 32) CTXp THR t30 t38 DT (Z_to_bv 64 0x5b4f8)) as (regsB & M1 & MB & RB10 & KB & U01 & G01).
  { zx_regv RA. } { unfold TP_A. rewrite <- R4. eapply reg_kept; [exact RA|reflexivity]. } { zx_regv RA. } { zx_regv RA. }
  { apply ret_ok_even. rewrite u_Z2bv64. reflexivity. }
  { lia. } { lia. }
  { eapply mem_def_grows; [exact G0|]. eapply mem_def_sub; [exact Hdsp|lia|lia]. }
  { eapply icells_unch; [exact U0|lia|exact IC]. }
  { unhide. clear - U0 Cctx Cthr Ct30 Ct38 Cdt Cdt18 Hsplo Hsphi Bc1 Bc2 Bt1 Bd1 Ac1 Ac2 Ac3 At1 At2 At3 Ad1 Ad2 Ad3.
    constructor; (eapply cellN_unch; [exact U0|lia|cbn; lia|intros r [<-|[]]; cbn; lia|assumption]). }
  { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { unhide; lia. } { unhide; lia. } { unhide; lia. }
  clear Cctx Cthr Ct30 Ct38 Cdt Cdt18 IC Ac1 Ac2 Ac3 At1 At2 At3 Ad1 Ad2 Ad3 Bc1 Bc2 Bt1 Bd1.
  assert (U1 : unch mem M1 [(sp - 256, sp)]).
  { eapply unch_trans; (eapply unch_widen; [eassumption|]); intros r [<-|[]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (G1 : mem_grows mem M1) by (eapply mem_grows_trans; eassumption).
  (* [comment removed for export] *)
  unhide. hide Hsp16; hide Hfs4096; hide Hret.
  assert (P2a : cellN SEGS_A M1 0x666328 8 FS) by (eapply cellN_unch; [exact U1|lia|cbn; lia|intros r [<-|[]]; cbn; lia|exact Ctls]).
  assert (P2b : cellN SEGS_A M1 (FS + 96) 1 0) by (eapply cellN_unch; [exact U1|lia|cbn; lia|intros r [<-|[]]; cbn; lia|exact Cgc]).
  assert (P2c : cellN SEGS_A M1 (FS + 88) 8 20) by (eapply cellN_unch; [exact U1|lia|cbn; lia|intros r [<-|[]]; cbn; lia|exact Clog]).
  assert (P2d : cellN SEGS_A M1 (FS + 32) 8 h) by (eapply cellN_unch; [exact U1|lia|cbn; lia|intros r [<-|[]]; cbn; lia|exact Ch]).
  assert (Cfl1 : forall q, 0 <= q < 1024 -> cellN SEGS_A M1 (FS + 34816 + q) 1 (fl q)).
  { intros q Hq. eapply cellN_unch; [exact U1|lia|cbn; lia|intros r [<-|[]]; cbn; lia|apply Cfl; lia]. }
  pose proof (mcells_unch mem M1 _ _ U1 ltac:(lia) MC) as [F1 F2 F3 F4 F5 F6 F7 F8].
  clear Ctls Cgc Clog Ch Cfl MC.
  hide Dfs.
  zx_run SEGS_A constr:(p2_ctx 32) 40%nat [0x5b568] (SCR [] []) [(10%bv : reg, ZL 0x666328)] [FS; h]
         constr:([Some (0x688000, 0x800000000000 - 11571200); Some (0, 18446744073709551615)]) regsB M1 rom 0x5b4f8.
  zx_use2 ZXB ltac:(zx_pins; exact RB10) ltac:(zx_lia) ltac:(kc1 P2a; kc1 P2b; kc1 P2c; kc1 P2d; exact I) ltac:(exact I) ltac:(exact I).
  clear ZF P2a P2b P2c P2d. rename regs0 into regsC. rename ZM into MC2. rename ZR into RC. rename ZE into EC.
  (* [comment removed for export] *)
  pose proof (probe_found fl 1024 h ltac:(lia) ltac:(lia) Hex) as (Hi0 & Hz & Hnz). cbv zeta in Hi0, Hz, Hnz.
  set (i0 := probe fl 1024 h (Z.to_nat 1024) 0) in *. clearbody i0.
  destruct (loop_4 rom (Z.to_nat i0) regsC M1 h 1024 (FS + 34816) fl) as (regsD & MD & D17 & D15 & D12 & KD).
  { zx_regv RC. } { zx_regv RC. } { zx_regv RC. } { zx_regv RC. }
  { lia. } { lia. } { lia. } { lia. }
  { intros j Hj. destruct (Hfl ((h + j) mod 1024) ltac:(lia)) as [_ [H0|H1]]; [|exact H1]. exfalso. apply (Hnz j); [lia|exact H0]. }
  { rewrite Z2Nat.id by lia. exact Hz. }
  { exact Cfl1. }
  rewrite Z2Nat.id in D17, D15, D12 by lia.
  set (p := (h + i0) mod 1024) in *.
  assert (Hp : 0 <= p < 1024) by (subst p; apply Z.mod_pos_bound; lia).
  clear Cfl1 Hfl Hex Hnz.
  assert (KC28 : keeps [2; 8] regsB regsC) by (eapply (keeps_of_zx _ _ _ _ _ _ EC RC); vm_compute; reflexivity).
  assert (HD2 : getr regsD 2%bv = Z_to_bv 64 (sp - 32)).
  { etransitivity; [exact (KD 2 ltac:(in_list))|]. etransitivity; [exact (KC28 2 ltac:(in_list))|].
    etransitivity; [exact (KB 2 ltac:(in_list))|]. zx_regv RA. }
  assert (HD8 : getr regsD 8%bv = Z_to_bv 64 sp).
  { etransitivity; [exact (KD 8 ltac:(in_list))|]. etransitivity; [exact (KC28 8 ltac:(in_list))|].
    etransitivity; [exact (KB 8 ltac:(in_list))|]. zx_regv RA. }
  clear KC28.
  (* [comment removed for export] *)
  assert (S1 : cellN SEGS_A M1 (sp - 8) 8 (bv_unsigned (getr regs (Z_to_bv 5 1)))).
  { eapply cellN_unch; [exact U01|lia|cbn; lia|intros r [<-|[]]; cbn; lia|exact S01]. }
  assert (S2 : cellN SEGS_A M1 (sp - 16) 8 (bv_unsigned (getr regs (Z_to_bv 5 8)))).
  { eapply cellN_unch; [exact U01|lia|cbn; lia|intros r [<-|[]]; cbn; lia|exact S02]. }
  assert (S3 : cellN SEGS_A M1 (sp - 24) 8 (bv_unsigned (getr regs (Z_to_bv 5 9)))).
  { eapply cellN_unch; [exact U01|lia|cbn; lia|intros r [<-|[]]; cbn; lia|exact S03]. }
  assert (S4 : cellN SEGS_A M1 (sp - 32) 8 (bv_unsigned (getr regs (Z_to_bv 5 18)))).
  { eapply cellN_unch; [exact U01|lia|cbn; lia|intros r [<-|[]]; cbn; lia|exact S04]. }
  assert (DF1 : mem_def M1 FS 11571200) by (eapply mem_def_grows; [exact G1|exact Hdfs]).
  assert (DS1 : mem_def M1 (2147450880 + FS / 8 + 4608) (1446400 - 4608)) by (eapply mem_def_grows; [exact G1|exact Hdsh]).
  clear U01 G01 U0 G0 Hdfs Hdsh S01 S02 S03 S04.
  (* [comment removed for export] *)
  destruct Hfsapp as [Hfsz | Hfsz];
    [ zx_run SEGS_A constr:(f_ctx (f_uvi_lo 1024) 34816 1024 4194304 128) 100%nat (@nil Z) (SCR [] []) constr:(f_pins 34816)
         [sp; FS; h + i0; p; bv_unsigned (getr regs (Z_to_bv 5 1)); bv_unsigned (getr regs (Z_to_bv 5 9));
          bv_unsigned (getr regs (Z_to_bv 5 18)); bv_unsigned (getr regs (Z_to_bv 5 8))]
         constr:(f_uvi_lo 1024) regsD M1 rom 0x5b5e0
    | zx_run SEGS_A constr:(f_ctx (f_uvi_hi 1024) 34816 1024 4194304 128) 100%nat (@nil Z) (SCR [] []) constr:(f_pins 34816)
         [sp; FS; h + i0; p; bv_unsigned (getr regs (Z_to_bv 5 1)); bv_unsigned (getr regs (Z_to_bv 5 9));
          bv_unsigned (getr regs (Z_to_bv 5 18)); bv_unsigned (getr regs (Z_to_bv 5 8))]
         constr:(f_uvi_hi 1024) regsD M1 rom 0x5b5e0 ].
  all: zx_use2 ZXB
    ltac:(zx_pins; pin_kept KD RC)
    ltac:(zx_lia)
    ltac:(kc1 S1; kc1 S2; kc1 S3; kc1 S4; kc1 F1; kc1 F2; kc1 F3; kc1 F4; kc1 F5; kc1 F6; kc1 F7; kc1 F8; exact I)
    ltac:(kwd DF1; kwd DF1; kwd DF1; kwd DS1; exact I)
    ltac:(unhide; zx_scs ltac:(first [eapply (store_ok_of_def_in _ _ _ _ _ _ DS1); lia | eapply (store_ok_of_def_in _ _ _ _ _ _ DF1); lia])).
  all: clear ZF S1 S2 S3 S4 F1 F2 F3 F4 F5 F6 F7 F8; rename regs0 into regsE.
  all: assert (RE1 : getr regsE 1%bv = ret) by (etransitivity; [zx_regv ZR|]; etransitivity; [apply Z_to_bv_bv_unsigned | exact R1]).
  (* [comment removed for export] *)
  all: unhide.
  all: eexists regsE, _, p.
  all: split;
   [ eapply msteps_trans; [exact MA|]; eapply msteps_trans; [exact MB|]; eapply msteps_trans; [exact MC2|];
     eapply msteps_trans; [exact MD|]; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact RE1 | exact Hret'] |].
  all: split;
   [ (* [comment removed for export] *)
     assert (K0 : keeps M_KEEP regs regsA) by (eapply (keeps_of_zx _ _ _ _ _ _ EA RA); vm_compute; reflexivity);
     assert (K1 : keeps M_KEEP regsA regsB) by (keeps_incl KB);
     assert (K2 : keeps M_KEEP regsB regsC) by (eapply (keeps_of_zx _ _ _ _ _ _ EC RC); vm_compute; reflexivity);
     assert (K3 : keeps M_KEEP regsC regsD) by (keeps_incl KD);
     assert (K4 : keeps M_KEEP regsD regsE) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity);
     assert (K : keeps M_KEEP regs regsE) by
      (eapply keeps_trans; [exact K0|]; eapply keeps_trans; [exact K1|]; eapply keeps_trans; [exact K2|];
       eapply keeps_trans; [exact K3|exact K4]);
     intros r Hr; cbn in Hr;
     repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end;
       first [ etransitivity; [zx_regv ZR|]; symmetry; exact R2
             | etransitivity; [zx_regv ZR|]; apply Z_to_bv_bv_unsigned
             | apply K; cbn; tauto ] |].
  all: split; [exact Hp|].
  all: split; [subst p; exact Hz|].
  all: split; [zx_regv ZR|].
  all: clear MA MB MC2 MD ZM ZE EA EC RA RC KB KD D17 D15 D12 RB10 RE1 R1 R2 R4.
  all: clear - Hsplo Hsphi Hfslo Hfshi Hfsz Hp U1 G1.
  all: split; [|split; [|split]];
   [ (* [comment removed for export] *) clear U1 G1; mbyte_go
   | (* [comment removed for export] *) clear U1 G1; mu64_go
   | (* [comment removed for export] *) clear U1 G1; change (1024 / 8) with 128; fill0_go
   | (* [comment removed for export] *)
     apply mem_frame_of_unch;
      [ eapply unch_trans;
         [ eapply unch_widen; [exact U1|]; intros r [<-|[]]; eexists; split; [left; reflexivity|cbn; lia]
         | clear U1 G1;
           lazymatch goal with |- unch _ _ [?r1; ?r2; ?r3; ?r4; ?r5; ?r6] =>
             apply (unch_widen _ _ [r6; r5; r4; r3; r2; r1]) end;
             [unchx | intros r Hr; exists r; split; [cbn [In] in Hr |- *; tauto | lia]] ]
      | eapply mem_grows_trans; [exact G1|]; growsx ] ].
Qed.
