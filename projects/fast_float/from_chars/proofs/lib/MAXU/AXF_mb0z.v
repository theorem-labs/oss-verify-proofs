(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits AxMalloc.

Module AXF_mb0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_n := EVar 32.
Definition e_sc := EVar 33.
Definition e_G := EVar 34.
Definition e_avail := EVar 35.
Definition e_idx := EVar 36.
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition LOWB := EAlu ALU_AND (EExt true 0 4 e_avail) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 e_avail)).
Definition DB := EAluw ALU_SRL (EMd M_MUL (ELit 125613361) LOWB) (ELit 27).
Definition sr_mb0 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 19 (ELit 98952)) 20 (e_sc)).
Definition kn_mb0 : list kentry :=
  [ KRange e_n 1 131051;
    KRange e_sc 0 47;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 0 (2^32-1);
    KWord (SA (ELit 0) 0x97c23) 1 (ELit 0);
    KWord (SA ACT 621800) 8 e_G;
    KWord (SA e_G 24) 4 e_avail;
    KRange DB 0 31;
    KWord (SA DB 98952) 1 e_idx;
    KWr (SA e_G 24) (ELit 4) ].
Definition scr_mb0 : scripts := SCR [] [] [].
Definition ss_mb0 := SS 0x53f2c sr_mb0 [] kn_mb0 37.
Definition RUN_mb0 := sym_exec SEGS 100 true [0x5405c; 0x54044] scr_mb0 ss_mb0 [].

Definition scr_mb0_T : scripts := SCR [true] [] [].
Definition RES_mb0_T := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044] scr_mb0_T ss_mb0 [].
Lemma RES_mb0_T_ok : sym_exec SEGS 100 true [0x5405c; 0x54044] scr_mb0_T (SS 0x53f2c sr_mb0 [] kn_mb0 37) [] = RES_mb0_T.
Proof. vm_compute. reflexivity. Qed.

Definition scr_mb0_F : scripts := SCR [false] [] [].
Definition RES_mb0_F := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044] scr_mb0_F ss_mb0 [].
Lemma RES_mb0_F_ok : sym_exec SEGS 100 true [0x5405c; 0x54044] scr_mb0_F (SS 0x53f2c sr_mb0 [] kn_mb0 37) [] = RES_mb0_F.
Proof. vm_compute. reflexivity. Qed.
End AXF_mb0.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb0z.AXF_mb0.
Import ListNotations AX2 AX2S.

Module AXF_mbt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_n := EVar 32.
Definition e_sc := EVar 33.
Definition e_G := EVar 34.
Definition e_avail := EVar 35.
Definition e_idx := EVar 36.
Definition LOWB := EAlu ALU_AND (EExt true 0 4 e_avail) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 e_avail)).
Definition DB := EAluw ALU_SRL (EMd M_MUL (ELit 125613361) LOWB) (ELit 27).
Definition sr_mbt := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 18 (e_G)) 19 (ELit 98952)) 20 (e_sc)).
Definition kn_mbt : list kentry :=
  [ KRange e_n 1 131051;
    KRange e_sc 0 47;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 0 (2^32-1);
    KWord (SA e_G 24) 4 e_avail;
    KRange DB 0 31;
    KWord (SA DB 98952) 1 e_idx;
    KWr (SA e_G 24) (ELit 4) ].
Definition scr_mbt : scripts := SCR [] [] [].
Definition ss_mbt := SS 0x53ff0 sr_mbt [] kn_mbt 37.
Definition RUN_mbt := sym_exec SEGS 100 true [0x5405c; 0x54044] scr_mbt ss_mbt [].

Definition scr_pbtf : scripts := SCR [false] [] [].
Definition RES_pbtf := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pbtf ss_mbt [].
Lemma RES_pbtf_ok : sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pbtf (SS 0x53ff0 sr_mbt [] kn_mbt 37) [] = RES_pbtf.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pbts : scripts := SCR [true] [] [].
Definition RES_pbts := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pbts ss_mbt [].
Lemma RES_pbts_ok : sym_exec SEGS 100 true [0x5405c; 0x54044] scr_pbts (SS 0x53ff0 sr_mbt [] kn_mbt 37) [] = RES_pbts.
Proof. vm_compute. reflexivity. Qed.
End AXF_mbt.

Module AXF_mbtz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits AxMalloc.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb0z.AXF_mbt.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record mbt_pre (regs : bvmap 5 word) (m : word -> option byte) (n sc G avail idx : Z) : Prop := {
  bt_R8 : getr regs 8 = wa n ; bt_R9 : getr regs 9 = wa 621712 ; bt_R18 : getr regs 18 = wa G ; bt_R19 : getr regs 19 = wa 98952 ;
  bt_R20 : getr regs 20 = wa sc ;
  bt_Rn : 1 <= n <= 131051 ; bt_Rsc : 0 <= sc <= 47 ; bt_RG : 1 <= G <= 2^63-1 ; bt_AG : G mod 8 = 0 ;
  bt_Rav : 0 <= avail <= 2^32-1 ; bt_Ridx : 0 <= idx <= 31 ;
  bt_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  bt_Rdb : 0 <= db_mach (wa avail) <= 31 ;
  bt_Mdb : rdn SEGS m (wa (db_mach (wa avail) + 98952)) 1 = Some (word_to_le_bytes 1 (wa idx)) ;
  bt_W : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (G + 24 + d)) k = true
}.

(* [comment removed for export] *)
Definition mbt_mem (m : word -> option byte) (G avail : Z) : word -> option byte :=
  wbytes m (wa (G + 24)) (word_to_le_bytes 4 (wa (avail - lowbit avail))).

Section MBT.
Context {fx : FPState}.

Definition mbt_env (regs : bvmap 5 word) (n sc G avail idx : Z) : env :=
  Env (reg_ev regs (fun k => wa (nth (k - 32) [n; sc; G; avail; idx] 0))) (fun _ => []).

#[using="Type"] Lemma mbt_regs_ok : forall regs m n sc G avail idx, mbt_pre regs m n sc G avail idx ->
  regs_ok (mbt_env regs n sc G avail idx) sr_mbt regs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc G avail idx P.
  apply (regs_ok_pin _ _ regs 20); [apply (regs_ok_pin _ _ regs 19); [apply (regs_ok_pin _ _ regs 18); [apply (regs_ok_pin _ _ regs 9);
    [apply (regs_ok_pin _ sr_id regs 8); [apply regs_ok_id|] |] |] |] |].
  - rewrite (bt_R8 _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (bt_R9 _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (bt_R18 _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (bt_R19 _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (bt_R20 _ _ _ _ _ _ _ P). reflexivity.
Qed.

#[using="Type"] Lemma mbt_know_ok : forall regs m n sc G avail idx, mbt_pre regs m n sc G avail idx ->
  know_ok SEGS (mbt_env regs n sc G avail idx) m kn_mbt.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc G avail idx P.
  destruct P as [R8 R9 R18 R19 R20 Rn Rsc RG AG Rav Ridx Mav Rdb Mdb W].
  set (E := mbt_env regs n sc G avail idx).
  assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by exact (u_wa_small _ (rng64 _ _ _ Rsc eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (ZDB : zeval E DB = db_mach (wa avail)) by reflexivity.
  unfold know_ok, kn_mbt.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: rewrite ?ZDB.
  all: cbn [zeval edenot e_n e_sc e_G e_avail e_idx a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: rewrite ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rn eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rsc eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rdb eq_refl eq_refl).
  all: litmods.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: try (intros d k Hd Hk; apply W; assumption).
  all: lia.
Qed.

Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

#[using="Type"] Lemma mbt_post_of : forall regs R n sc G avail idx sres (l : list nat),
  regs_ok (mbt_env regs n sc G avail idx) sres R ->
  (forall k, In k l -> (k < 32)%nat) ->
  (forall k, In k l -> sr_get sres (Z_to_bv 5 (Z.of_nat k)) = EVar k) ->
  forall k, In k l -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs R n sc G avail idx sres l HR Hl Hs k Hk. rewrite (HR _), (Hs k Hk). cbn [edenot ev mbt_env]. unfold reg_ev.
  replace (Nat.ltb k 32) with true by (symmetry; apply Nat.ltb_lt; apply Hl; exact Hk). reflexivity.
Qed.

#[using="Type"] Lemma mbt_lowb : forall regs n sc G avail idx, 0 <= avail <= 2^32-1 ->
  zeval (mbt_env regs n sc G avail idx) LOWB mod 2^64 = lowb_mach (wa avail).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs n sc G avail idx Rav. rewrite <- u_wa, <- zeval_sound. cbn [edenot LOWB e_avail]. rewrite u_and64. reflexivity.
Qed.

#[using="Type"] Theorem mbt_fast : forall regs m rom n sc G avail idx, mbt_pre regs m n sc G avail idx -> avail <> 0 ->
  exists R, msteps SEGS (mkst regs (wa 0x53ff0) m rom) (mkst R (wa 0x5405c) (mbt_mem m G avail) rom)
         /\ getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 18 = wa G /\ getr R 19 = wa idx /\ getr R 20 = wa sc
         /\ (forall k, In k [1;2;3;4;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc G avail idx P Hnz.
  pose proof (mbt_regs_ok regs m n sc G avail idx P) as HR. pose proof (mbt_know_ok regs m n sc G avail idx P) as HK.
  pose proof P as P'. destruct P' as [R8 R9 R18 R19 R20 Rn Rsc RG AG Rav Ridx Mav Rdb Mdb W].
  pose proof (mbt_lowb regs n sc G avail idx Rav) as LB.
  set (E := mbt_env regs n sc G avail idx) in *.
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  pose proof (lowb_mach_mod32 avail ltac:(lia)) as LB32.
  destruct (lowbit_pow avail ltac:(lia)) as (LP & Rj).
  assert (LNZ : lowb_mach (wa avail) <> 0).
  { intros E0. rewrite E0 in LB32. rewrite LP in LB32. change (0 mod 2^32) with 0 in LB32.
    pose proof (Z.pow_pos_nonneg 2 (ctz32 avail) ltac:(lia) ltac:(lia)). lia. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_pbtf))).
  { cbn [RES_pbtf fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z. all: try (change (EAlu ALU_AND (EExt true 0 4 (EVar 35)) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 (EVar 35)))) with LOWB).
    all: first [ (rewrite br_eq_z, LB; change (zeval E (ELit 0) mod 2^64) with 0; apply Z.eqb_neq; exact LNZ)
               | (rewrite br_eq_z; cbn [zeval edenot]; rewrite Z34; change (0 mod 2^64) with 0; rewrite (Z.mod_small G) by lia;
                  apply Z.eqb_neq; lia) ]. }
  destruct (run_sound SEGS 100 [0x5405c; 0x54044] scr_pbtf 0x53ff0 sr_mbt kn_mbt 37 _ _ _ E m rom regs RES_pbtf_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [RES_pbtf fst snd s_pc s_log mem_denot] in Hms. unfold mbt_mem.
    replace (adenot E {| a_base := EVar 34; a_off := 24 |}) with (wa (G + 24)) in Hms by (rewrite adenot_z; cbn [zeval edenot]; rewrite Z34; reflexivity).
    assert (XE : zeval E (EExt true 0 4 (EVar 35)) mod 2^64 = bv_unsigned (ext_val true 0 4 (wa avail))) by (rewrite <- u_wa, <- zeval_sound; reflexivity).
    pose proof (ext4_mod32 avail ltac:(lia)) as HX.
    change (EAlu ALU_AND (EExt true 0 4 (EVar 35)) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 (EVar 35)))) with LOWB in Hms.
    replace (word_to_le_bytes 4 (edenot E (EAluw ALU_SUB (EExt true 0 4 (EVar 35)) LOWB))) with (word_to_le_bytes 4 (wa (avail - lowbit avail))) in Hms;
      [exact Hms|].
    rewrite edenot_subw'. apply le_wa_eqm; [|lia]. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
    rewrite swrap32_mod, XE, LB.
    rewrite (Zminus_mod (bv_unsigned (ext_val true 0 4 (wa avail))) (lowb_mach (wa avail))), HX, LB32. reflexivity.
  - clear Hms.      (* [comment removed for export] *)
    assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
    assert (Z33 : bv_unsigned (ev E 33) = sc) by exact (u_wa_small _ (rng64 _ _ _ Rsc eq_refl)).
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z36; unfold ext_Z; cbv zeta;
            rewrite (Z.mod_small idx) by lia; change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; apply Z.mod_small; cbn; lia|].
    split; [srg HR'; reflexivity|].
    apply (mbt_post_of regs R n sc G avail idx _ _ HR'); [intros k Hk; cbn [In] in Hk; lia|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]). destruct Hk.
Qed.

#[using="Type"] Theorem mbt_slow : forall regs m rom n sc G avail idx, mbt_pre regs m n sc G avail idx -> avail = 0 ->
  exists R, msteps SEGS (mkst regs (wa 0x53ff0) m rom) (mkst R (wa 0x54044) m rom)
         /\ getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa n /\ getr R 18 = wa sc
         /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc
         /\ (forall k, In k [1;2;3;4;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc G avail idx P Hz.
  pose proof (mbt_regs_ok regs m n sc G avail idx P) as HR. pose proof (mbt_know_ok regs m n sc G avail idx P) as HK.
  pose proof P as P'. destruct P' as [R8 R9 R18 R19 R20 Rn Rsc RG AG Rav Ridx Mav Rdb Mdb W].
  pose proof (mbt_lowb regs n sc G avail idx Rav) as LB.
  set (E := mbt_env regs n sc G avail idx) in *.
  assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by exact (u_wa_small _ (rng64 _ _ _ Rsc eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (L0 : lowb_mach (wa avail) = 0) by (subst avail; vm_compute; reflexivity).
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_pbts))).
  { cbn [RES_pbts fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z. all: try (change (EAlu ALU_AND (EExt true 0 4 (EVar 35)) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 (EVar 35)))) with LOWB).
    all: first [ (rewrite br_eq_z, LB, L0; reflexivity)
               | (rewrite br_eq_z; cbn [zeval edenot]; rewrite Z34; change (0 mod 2^64) with 0; rewrite (Z.mod_small G) by lia;
                  apply Z.eqb_neq; lia) ]. }
  destruct (run_sound SEGS 100 [0x5405c; 0x54044] scr_pbts 0x53ff0 sr_mbt kn_mbt 37 _ _ _ E m rom regs RES_pbts_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split; [cbn [RES_pbts fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
  clear Hms.      (* [comment removed for export] *)
  split; [srg HR'; reflexivity|].
  split; [srg HR'; reflexivity|].
  split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z33; first [reflexivity | apply Z.mod_small; lia]|].
  split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z32; reflexivity|].
  split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z33; first [reflexivity | apply Z.mod_small; lia]|].
  split; [srg HR'; reflexivity|].
  split; [srg HR'; reflexivity|].
  apply (mbt_post_of regs R n sc G avail idx _ _ HR'); [intros k Hk; cbn [In] in Hk; lia|].
  intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]). destruct Hk.
Qed.

End MBT.
End AXF_mbtz.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Record mb0_pre (regs : bvmap 5 word) (m : word -> option byte) (n sc G avail idx : Z) : Prop := {
  b0_R8 : getr regs 8 = wa n ; b0_R9 : getr regs 9 = wa 621712 ; b0_R19 : getr regs 19 = wa 98952 ; b0_R20 : getr regs 20 = wa sc ;
  b0_Rn : 1 <= n <= 131051 ; b0_Rsc : 0 <= sc <= 47 ; b0_RG : 1 <= G <= 2^63-1 ; b0_AG : G mod 8 = 0 ;
  b0_Rav : 0 <= avail <= 2^32-1 ; b0_Ridx : 0 <= idx <= 31 ;
  b0_Mnl : rdn SEGS m (wa 0x97c23) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  b0_Mact : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  b0_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  b0_Rdb : 0 <= db_mach (wa avail) <= 31 ;
  b0_Mdb : rdn SEGS m (wa (db_mach (wa avail) + 98952)) 1 = Some (word_to_le_bytes 1 (wa idx)) ;
  b0_W : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (G + 24 + d)) k = true
}.

(* [comment removed for export] *)
Definition mb0_mem (m : word -> option byte) (G avail : Z) : word -> option byte :=
  wbytes m (wa (G + 24)) (word_to_le_bytes 4 (wa (avail - lowbit avail))).

Section MB0.
Context {fx : FPState}.

Definition mb0_env (regs : bvmap 5 word) (n sc G avail idx : Z) : env :=
  Env (reg_ev regs (fun k => wa (nth (k - 32) [n; sc; G; avail; idx] 0))) (fun _ => []).

#[using="Type"] Lemma mb0_regs_ok : forall regs m n sc G avail idx, mb0_pre regs m n sc G avail idx ->
  regs_ok (mb0_env regs n sc G avail idx) sr_mb0 regs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc G avail idx P.
  apply (regs_ok_pin _ _ regs 20); [apply (regs_ok_pin _ _ regs 19); [apply (regs_ok_pin _ _ regs 9);
    [apply (regs_ok_pin _ sr_id regs 8); [apply regs_ok_id|] |] |] |].
  - rewrite (b0_R8 _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (b0_R9 _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (b0_R19 _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (b0_R20 _ _ _ _ _ _ _ P). reflexivity.
Qed.

#[using="Type"] Lemma mb0_know_ok : forall regs m n sc G avail idx, mb0_pre regs m n sc G avail idx ->
  know_ok SEGS (mb0_env regs n sc G avail idx) m kn_mb0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc G avail idx P.
  destruct P as [R8 R9 R19 R20 Rn Rsc RG AG Rav Ridx Mnl Mact Mav Rdb Mdb W].
  set (E := mb0_env regs n sc G avail idx).
  assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by exact (u_wa_small _ (rng64 _ _ _ Rsc eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (ZDB : zeval E DB = db_mach (wa avail)) by reflexivity.
  unfold know_ok, kn_mb0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: rewrite ?ZDB.
  all: cbn [zeval edenot e_n e_sc e_G e_avail e_idx ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: rewrite ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rn eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rsc eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rdb eq_refl eq_refl).
  all: litmods.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: try (intros d k Hd Hk; apply W; assumption).
  all: try (rewrite (Z.mod_small (8 * sc)) by lia; first [assumption | lia]).
  all: lia.
Qed.

Definition keep_b0 : list nat := [1;2;3;4;8;9;18;20;21;22;23;24;25;26;27]%nat.

Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

#[using="Type"] Lemma mb0_post_of : forall regs R n sc G avail idx sres (l : list nat),
  regs_ok (mb0_env regs n sc G avail idx) sres R ->
  (forall k, In k l -> (k < 32)%nat) ->
  (forall k, In k l -> sr_get sres (Z_to_bv 5 (Z.of_nat k)) = EVar k) ->
  forall k, In k l -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs R n sc G avail idx sres l HR Hl Hs k Hk. rewrite (HR _), (Hs k Hk). cbn [edenot ev mb0_env]. unfold reg_ev.
  replace (Nat.ltb k 32) with true by (symmetry; apply Nat.ltb_lt; apply Hl; exact Hk). reflexivity.
Qed.

#[using="Type"] Lemma mb0_lowb : forall regs n sc G avail idx, 0 <= avail <= 2^32-1 ->
  zeval (mb0_env regs n sc G avail idx) LOWB mod 2^64 = lowb_mach (wa avail).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs n sc G avail idx Rav. rewrite <- u_wa, <- zeval_sound. cbn [edenot LOWB e_avail]. rewrite u_and64. reflexivity.
Qed.

#[using="Type"] Theorem mb0_fast : forall regs m rom n sc G avail idx, mb0_pre regs m n sc G avail idx -> avail <> 0 ->
  exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x5405c) (mb0_mem m G avail) rom)
         /\ getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 18 = wa G /\ getr R 19 = wa idx /\ getr R 20 = wa sc
         /\ (forall k, In k [1;2;3;4;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc G avail idx P Hnz.
  pose proof (mb0_regs_ok regs m n sc G avail idx P) as HR. pose proof (mb0_know_ok regs m n sc G avail idx P) as HK.
  pose proof P as P'. destruct P' as [R8 R9 R19 R20 Rn Rsc RG AG Rav Ridx Mnl Mact Mav Rdb Mdb W].
  pose proof (mb0_lowb regs n sc G avail idx Rav) as LB.
  set (E := mb0_env regs n sc G avail idx) in *.
  assert (Z34 : bv_unsigned (ev E 34) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  pose proof (lowb_mach_mod32 avail ltac:(lia)) as LB32.
  destruct (lowbit_pow avail ltac:(lia)) as (LP & Rj).
  assert (LNZ : lowb_mach (wa avail) <> 0).
  { intros E0. rewrite E0 in LB32. rewrite LP in LB32. change (0 mod 2^32) with 0 in LB32.
    pose proof (Z.pow_pos_nonneg 2 (ctz32 avail) ltac:(lia) ltac:(lia)). lia. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_mb0_F))).
  { cbn [RES_mb0_F fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z. all: change (EAlu ALU_AND (EExt true 0 4 (EVar 35)) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 (EVar 35)))) with LOWB.
    all: rewrite br_eq_z, LB. change (zeval E (ELit 0) mod 2^64) with 0. apply Z.eqb_neq. exact LNZ. }
  destruct (run_sound SEGS 100 [0x5405c; 0x54044] scr_mb0_F 0x53f2c sr_mb0 kn_mb0 37 _ _ _ E m rom regs RES_mb0_F_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [RES_mb0_F fst snd s_pc s_log mem_denot] in Hms. unfold mb0_mem.
    replace (adenot E {| a_base := EVar 34; a_off := 24 |}) with (wa (G + 24)) in Hms by (rewrite adenot_z; cbn [zeval edenot]; rewrite Z34; reflexivity).
    assert (XE : zeval E (EExt true 0 4 (EVar 35)) mod 2^64 = bv_unsigned (ext_val true 0 4 (wa avail))) by (rewrite <- u_wa, <- zeval_sound; reflexivity).
    pose proof (ext4_mod32 avail ltac:(lia)) as HX.
    change (EAlu ALU_AND (EExt true 0 4 (EVar 35)) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 (EVar 35)))) with LOWB in Hms.
    replace (word_to_le_bytes 4 (edenot E (EAluw ALU_SUB (EExt true 0 4 (EVar 35)) LOWB))) with (word_to_le_bytes 4 (wa (avail - lowbit avail))) in Hms;
      [exact Hms|].
    rewrite edenot_subw'. apply le_wa_eqm; [|lia]. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
    rewrite swrap32_mod, XE, LB.
    rewrite (Zminus_mod (bv_unsigned (ext_val true 0 4 (wa avail))) (lowb_mach (wa avail))), HX, LB32. reflexivity.
  - clear Hms.      (* [comment removed for export] *)
    assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
    assert (Z33 : bv_unsigned (ev E 33) = sc) by exact (u_wa_small _ (rng64 _ _ _ Rsc eq_refl)).
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z36; unfold ext_Z; cbv zeta;
            rewrite (Z.mod_small idx) by lia; change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; apply Z.mod_small; cbn; lia|].
    split; [srg HR'; reflexivity|].
    apply (mb0_post_of regs R n sc G avail idx _ _ HR'); [intros k Hk; cbn [In] in Hk; lia|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]). destruct Hk.
Qed.

#[using="Type"] Theorem mb0_slow : forall regs m rom n sc G avail idx, mb0_pre regs m n sc G avail idx -> avail = 0 ->
  exists R, msteps SEGS (mkst regs (wa 0x53f2c) m rom) (mkst R (wa 0x54044) m rom)
         /\ getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa sc /\ getr R 11 = wa n /\ getr R 18 = wa sc
         /\ getr R 19 = wa 98952 /\ getr R 20 = wa sc
         /\ (forall k, In k [1;2;3;4;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc G avail idx P Hz.
  pose proof (mb0_regs_ok regs m n sc G avail idx P) as HR. pose proof (mb0_know_ok regs m n sc G avail idx P) as HK.
  pose proof P as P'. destruct P' as [R8 R9 R19 R20 Rn Rsc RG AG Rav Ridx Mnl Mact Mav Rdb Mdb W].
  pose proof (mb0_lowb regs n sc G avail idx Rav) as LB.
  set (E := mb0_env regs n sc G avail idx) in *.
  assert (Z32 : bv_unsigned (ev E 32) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by exact (u_wa_small _ (rng64 _ _ _ Rsc eq_refl)).
  assert (L0 : lowb_mach (wa avail) = 0) by (subst avail; vm_compute; reflexivity).
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_mb0_T))).
  { cbn [RES_mb0_T fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z. all: change (EAlu ALU_AND (EExt true 0 4 (EVar 35)) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 (EVar 35)))) with LOWB.
    all: rewrite br_eq_z, LB, L0. reflexivity. }
  destruct (run_sound SEGS 100 [0x5405c; 0x54044] scr_mb0_T 0x53f2c sr_mb0 kn_mb0 37 _ _ _ E m rom regs RES_mb0_T_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split; [cbn [RES_mb0_T fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
  clear Hms.      (* [comment removed for export] *)
  split; [srg HR'; reflexivity|].
  split; [srg HR'; reflexivity|].
  split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z33; first [reflexivity | apply Z.mod_small; lia]|].
  split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z32; reflexivity|].
  split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z33; first [reflexivity | apply Z.mod_small; lia]|].
  split; [srg HR'; reflexivity|].
  split; [srg HR'; reflexivity|].
  apply (mb0_post_of regs R n sc G avail idx _ _ HR'); [intros k Hk; cbn [In] in Hk; lia|].
  intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]). destruct Hk.
Qed.

End MB0.
