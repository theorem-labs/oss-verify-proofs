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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits AxMalloc MngZ AXF_mb0z.

Module AXF_tk.
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

Definition e_G := EVar 32.
Definition e_avail := EVar 33.
Definition e_idx := EVar 34.
Definition LOWB := EAlu ALU_AND (EExt true 0 4 e_avail) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 e_avail)).
Definition DB := EAluw ALU_SRL (EMd M_MUL (ELit 125613361) LOWB) (ELit 27).
Definition sr_tk := (sr_upd (sr_upd sr_id 10 (e_G)) 11 (EExt true 0 4 e_avail)).
Definition kn_tk : list kentry :=
  [ KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 1 (2^32-1);
    KWr (SA e_G 24) (ELit 4);
    KRange DB 0 31;
    KWord (SA DB 98952) 1 e_idx;
    KDisj (SA DB 98952) (ELit 1) (SA e_G 24) (ELit 4) ].
Definition scr_tk : scripts := SCR [false] [] [].
Definition ss_tk := SS 0x54248 sr_tk [] kn_tk 35.
Definition RUN_tk := sym_exec SEGS 100 true [0x54908] scr_tk ss_tk [].

Definition scr_ptk : scripts := SCR [false] [] [].
Definition RES_ptk := Eval vm_compute in sym_exec SEGS 100 true [0x54908] scr_ptk ss_tk [].
Lemma RES_ptk_ok : sym_exec SEGS 100 true [0x54908] scr_ptk (SS 0x54248 sr_tk [] kn_tk 35) [] = RES_ptk.
Proof. vm_compute. reflexivity. Qed.
End AXF_tk.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Record tk_pre (regs : bvmap 5 word) (m : word -> option byte) (G avail idx : Z) : Prop := {
  tk_R10 : getr regs 10 = wa G ; tk_R11 : getr regs 11 = wa (ext_Z true 0 4 avail) ;
  tk_RG : 1 <= G <= 2^63-1 ; tk_AG : G mod 8 = 0 ; tk_Rav : 1 <= avail <= 2^32-1 ; tk_Ridx : 0 <= idx <= 31 ;
  tk_Rdb : 0 <= db_mach (wa avail) <= 31 ;
  tk_Mdb : rdn SEGS m (wa (db_mach (wa avail) + 98952)) 1 = Some (word_to_le_bytes 1 (wa idx)) ;
  tk_W : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (G + 24 + d)) k = true ;
  tk_D : db_mach (wa avail) + 98952 + 1 <= G + 24 \/ G + 24 + 4 <= db_mach (wa avail) + 98952
}.

Section TK.
Context {fx : FPState}.

Definition tk_env (regs : bvmap 5 word) (G avail idx : Z) : env :=
  Env (reg_ev regs (fun k => wa (nth (k - 32) [G; avail; idx] 0))) (fun _ => []).

#[using="Type"] Theorem tk_arm : forall regs m rom G avail idx, tk_pre regs m G avail idx ->
  exists R, msteps SEGS (mkst regs (wa 0x54248) m rom) (mkst R (wa 0x54908) (mb0_mem m G avail) rom)
         /\ getr R 10 = wa idx
         /\ (forall k, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G avail idx P.
  pose proof P as P'. destruct P' as [R10 R11 RG AG Rav Ridx Rdb Mdb W D].
  set (E := tk_env regs G avail idx).
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (HR : regs_ok E AXF_tk.sr_tk regs).
  { apply (regs_ok_pin _ _ regs 11); [apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|] |].
    - rewrite R10. reflexivity.
    - rewrite R11, zeval_sound. cbn [zeval edenot AXF_tk.e_avail]. rewrite Z33. rewrite (mod64_of_range _ _ _ Rav eq_refl eq_refl). reflexivity. }
  assert (ZDB : zeval E AXF_tk.DB = db_mach (wa avail)) by reflexivity.
  assert (HK : know_ok SEGS E m AXF_tk.kn_tk).
  { unfold know_ok, AXF_tk.kn_tk.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: rewrite ?ZDB.
    all: cbn [zeval edenot AXF_tk.e_G AXF_tk.e_avail AXF_tk.e_idx a_base a_off].
    all: rewrite ?Z32, ?Z33, ?Z34.
    all: rewrite ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rdb eq_refl eq_refl).
    all: litmods.
    all: try zlit.
    all: try assumption.
    all: try zrange.
    all: try (intros d k Hd Hk; apply W; assumption).
    all: lia. }
  assert (LB : zeval E AXF_tk.LOWB mod 2^64 = lowb_mach (wa avail)).
  { rewrite <- u_wa, <- zeval_sound. cbn [edenot AXF_tk.LOWB AXF_tk.e_avail]. rewrite u_and64. reflexivity. }
  pose proof (lowb_mach_mod32 avail ltac:(lia)) as LB32.
  destruct (lowbit_pow avail ltac:(lia)) as (LP & Rj).
  assert (LNZ : lowb_mach (wa avail) <> 0).
  { intros E0. rewrite E0 in LB32. rewrite LP in LB32. change (0 mod 2^32) with 0 in LB32.
    pose proof (Z.pow_pos_nonneg 2 (ctz32 avail) ltac:(lia) ltac:(lia)). lia. }
  assert (Hsc : scs_denot SEGS m E (snd (fst AXF_tk.RES_ptk))).
  { cbn [AXF_tk.RES_ptk fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z. all: change (EAlu ALU_AND (EExt true 0 4 (EVar 33)) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 (EVar 33)))) with AXF_tk.LOWB.
    all: rewrite br_eq_z, LB. change (zeval E (ELit 0) mod 2^64) with 0. apply Z.eqb_neq. exact LNZ. }
  destruct (run_sound SEGS 100 [0x54908] AXF_tk.scr_ptk 0x54248 AXF_tk.sr_tk AXF_tk.kn_tk 35 _ _ _ E m rom regs AXF_tk.RES_ptk_ok HR HK Hsc)
    as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_tk.RES_ptk fst snd s_pc s_log mem_denot] in Hms. unfold mb0_mem.
    replace (adenot E {| a_base := EVar 32; a_off := 24 |}) with (wa (G + 24)) in Hms by (rewrite adenot_z; cbn [zeval edenot]; rewrite Z32; reflexivity).
    assert (XE : zeval E (EExt true 0 4 (EVar 33)) mod 2^64 = bv_unsigned (ext_val true 0 4 (wa avail))) by (rewrite <- u_wa, <- zeval_sound; reflexivity).
    pose proof (ext4_mod32 avail ltac:(lia)) as HX.
    change (EAlu ALU_AND (EExt true 0 4 (EVar 33)) (EAluw ALU_SUB (ELit 0) (EExt true 0 4 (EVar 33)))) with AXF_tk.LOWB in Hms.
    replace (word_to_le_bytes 4 (edenot E (EAluw ALU_SUB (EExt true 0 4 (EVar 33)) AXF_tk.LOWB))) with (word_to_le_bytes 4 (wa (avail - lowbit avail))) in Hms;
      [exact Hms|].
    rewrite edenot_subw'. apply le_wa_eqm; [|lia]. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
    rewrite swrap32_mod, XE, LB.
    rewrite (Zminus_mod (bv_unsigned (ext_val true 0 4 (wa avail))) (lowb_mach (wa avail))), HX, LB32. reflexivity.
  - clear Hms.      (* [comment removed for export] *)
    split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z34; unfold ext_Z; cbv zeta;
            rewrite (Z.mod_small idx) by lia; change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; apply Z.mod_small; cbn; lia|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TK.
