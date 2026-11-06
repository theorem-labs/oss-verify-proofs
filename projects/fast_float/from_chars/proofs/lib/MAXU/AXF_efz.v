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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits.

Module AXF_efa1.
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
Definition e_idx := EVar 33.
Definition e_n := EVar 34.
Definition e_ctr := EVar 35.
Definition e_W := EVar 36.
Definition e_mem := EVar 37.
Definition e_sz := EVar 38.
Definition e_h3 := EVar 39.
Definition e_h16 := EVar 40.
Definition TABSZ := EMd M_MUL (ELit 2) (EAlu ALU_SRL (EAlu ALU_SRL e_W (ELit 5)) (ELit 1)).
Definition SLOT := EAlu ALU_ADD e_mem (EMd M_MUL (EMd M_MUL (ELit 16) e_sz) e_idx).
Definition sr_efa1 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G)) 11 (e_idx)) 12 (e_n)) 13 (e_ctr)).
Definition kn_efa1 : list kentry :=
  [ KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_n 1 131051;
    KRange e_ctr 0 (2^64-1);
    KRange e_W 0 3071;
    KRange e_mem 1 (2^63-1);
    KRange e_sz 1 8191;
    KRange e_h3 0 255;
    KRange e_h16 0 65535;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 16) 8 e_mem;
    KWord (SA TABSZ 98984) 2 e_sz;
    KRange SLOT 1 (2^63-1);
    KWord (SA SLOT 12) 1 (ELit 0);
    KWord (SA SLOT 13) 1 e_h3;
    KWord (SA SLOT 14) 2 e_h16 ].
Definition scr_efa1 : scripts := SCR [] [] [].
Definition ss_efa1 := SS 0x5494c sr_efa1 [] kn_efa1 41.
Definition RUN_efa1 := sym_exec SEGS 200 true [0x549c8] scr_efa1 ss_efa1 [].

Definition scr_efa1_T : scripts := SCR [true] [] [].
Definition RES_efa1_T := Eval vm_compute in sym_exec SEGS 200 true [0x549c8] scr_efa1_T ss_efa1 [].
Lemma RES_efa1_T_ok : sym_exec SEGS 200 true [0x549c8] scr_efa1_T (SS 0x5494c sr_efa1 [] kn_efa1 41) [] = RES_efa1_T.
Proof. vm_compute. reflexivity. Qed.

Definition scr_efa1_F : scripts := SCR [false] [] [].
Definition RES_efa1_F := Eval vm_compute in sym_exec SEGS 200 true [0x549c8] scr_efa1_F ss_efa1 [].
Lemma RES_efa1_F_ok : sym_exec SEGS 200 true [0x549c8] scr_efa1_F (SS 0x5494c sr_efa1 [] kn_efa1 41) [] = RES_efa1_F.
Proof. vm_compute. reflexivity. Qed.
End AXF_efa1.


Module AXF_efa2.
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

Definition e_t0 := EVar 32.
Definition e_sl := EVar 33.
Definition e_off0 := EVar 34.
Definition sr_efa2 := (sr_upd (sr_upd (sr_upd sr_id 5 (e_t0)) 6 (e_sl)) 17 (e_off0)).
Definition kn_efa2 : list kentry :=
  [ KRange e_t0 0 131071;
    KRange e_sl 0 8191;
    KRange e_off0 0 255 ].
Definition scr_efa2 : scripts := SCR [] [] [].
Definition ss_efa2 := SS 0x549c8 sr_efa2 [] kn_efa2 35.
Definition RUN_efa2 := sym_exec SEGS 100 true [0x54a04] scr_efa2 ss_efa2 [].

Definition scr_efa2_T : scripts := SCR [true] [] [].
Definition RES_efa2_T := Eval vm_compute in sym_exec SEGS 100 true [0x54a04] scr_efa2_T ss_efa2 [].
Lemma RES_efa2_T_ok : sym_exec SEGS 100 true [0x54a04] scr_efa2_T (SS 0x549c8 sr_efa2 [] kn_efa2 35) [] = RES_efa2_T.
Proof. vm_compute. reflexivity. Qed.

Definition scr_efa2_FT : scripts := SCR [false; true] [] [].
Definition RES_efa2_FT := Eval vm_compute in sym_exec SEGS 100 true [0x54a04] scr_efa2_FT ss_efa2 [].
Lemma RES_efa2_FT_ok : sym_exec SEGS 100 true [0x54a04] scr_efa2_FT (SS 0x549c8 sr_efa2 [] kn_efa2 35) [] = RES_efa2_FT.
Proof. vm_compute. reflexivity. Qed.
End AXF_efa2.

From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.

Module AXF_efa1z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa2.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record efa_pre (regs : bvmap 5 word) (m : word -> option byte) (G idx n ctr W mem sz h3 h16 : Z) : Prop := {
  ea_R10 : getr regs 10 = wa G ; ea_R11 : getr regs 11 = wa idx ; ea_R12 : getr regs 12 = wa n ; ea_R13 : getr regs 13 = wa ctr ;
  ea_RG : 1 <= G <= 2^63-1 ; ea_AG : G mod 8 = 0 ; ea_Ridx : 0 <= idx <= 31 ; ea_Rn : 1 <= n <= 131051 ;
  ea_Rctr : 0 <= ctr <= 2^64-1 ; ea_RW : 0 <= W <= 3071 ; ea_Rmem : 1 <= mem <= 2^63-1 ; ea_Rsz : 1 <= sz <= 8191 ;
  ea_Rh3 : 0 <= h3 <= 255 ; ea_Rh16 : 0 <= h16 <= 65535 ;
  ea_RSLOT : 1 <= mem + 16 * sz * idx <= 2^63-1 ;
  ea_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  ea_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa mem)) ;
  ea_Msz : rdn SEGS m (wa (2 * Z.shiftr W 6 + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz)) ;
  ea_M12 : rdn SEGS m (wa (mem + 16 * sz * idx + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  ea_M13 : rdn SEGS m (wa (mem + 16 * sz * idx + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  ea_M14 : rdn SEGS m (wa (mem + 16 * sz * idx + 14)) 2 = Some (word_to_le_bytes 2 (wa h16)) ;
  ea_fit : n + 4 <= 16 * sz
}.

(* [comment removed for export] *)
Definition ef_slack (sz n : Z) : Z := Z.shiftr (16 * sz - n - 4) 4.
Definition ef_off0 (ctr h3 h16 : Z) : Z := Z.land (if h3 =? 0 then ctr else h16 + 1) 255.
Definition ef_mask (sl : Z) : Z := let m1 := Z.lor sl (Z.shiftr sl 1) in let m2 := Z.lor m1 (Z.shiftr m1 2) in Z.lor m2 (Z.shiftr m2 4).
Definition ef_off (sl off0 : Z) : Z :=
  if off0 <=? sl then off0 else let off1 := Z.land off0 (ef_mask sl) in if sl <? off1 then off1 - (sl + 1) else off1.

Lemma shiftr_shiftr_5_1 : forall W, 0 <= W -> Z.shiftr (Z.shiftr W 5) 1 = Z.shiftr W 6.
Proof. intros W HW. rewrite Z.shiftr_shiftr by lia. reflexivity. Qed.

Lemma land255_range : forall x, 0 <= Z.land x 255 <= 255.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2^8) ltac:(lia)). change (Z.ones 8) with 255. lia. Qed.

Section EFA.
Context {fx : FPState}.

Definition efa_env (regs : bvmap 5 word) (G idx n ctr W mem sz h3 h16 : Z) : env :=
  Env (reg_ev regs (fun k => wa (nth (k - 32) [G; idx; n; ctr; W; mem; sz; h3; h16] 0))) (fun _ => []).

#[using="Type"] Lemma efa_regs_ok : forall regs m G idx n ctr W mem sz h3 h16, efa_pre regs m G idx n ctr W mem sz h3 h16 ->
  regs_ok (efa_env regs G idx n ctr W mem sz h3 h16) sr_efa1 regs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx n ctr W mem sz h3 h16 P.
  apply (regs_ok_pin _ _ regs 13); [apply (regs_ok_pin _ _ regs 12); [apply (regs_ok_pin _ _ regs 11);
    [apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|] |] |] |].
  - rewrite (ea_R10 _ _ _ _ _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (ea_R11 _ _ _ _ _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (ea_R12 _ _ _ _ _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (ea_R13 _ _ _ _ _ _ _ _ _ _ _ P). reflexivity.
Qed.

#[using="Type"] Lemma efa_know_ok : forall regs m G idx n ctr W mem sz h3 h16, efa_pre regs m G idx n ctr W mem sz h3 h16 ->
  know_ok SEGS (efa_env regs G idx n ctr W mem sz h3 h16) m kn_efa1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx n ctr W mem sz h3 h16 P.
  destruct P as [R10 R11 R12 R13 RG AG Ridx Rn Rctr RW Rmem Rsz Rh3 Rh16 RSLOT MW Mmem Msz M12 M13 M14 Fit].
  set (E := efa_env regs G idx n ctr W mem sz h3 h16).
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = ctr) by exact (u_wa_small _ (rng64 _ _ _ Rctr eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = h16) by exact (u_wa_small _ (rng64 _ _ _ Rh16 eq_refl)).
  unfold know_ok, kn_efa1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) ].
  all: cbn [zeval edenot e_G e_idx e_n e_ctr e_W e_mem e_sz e_h3 e_h16 TABSZ SLOT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
  all: rewrite ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl),
         ?(mod64_of_range _ _ _ RW eq_refl eq_refl), ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rh16 eq_refl eq_refl), ?(mod64_of_range _ _ _ RSLOT eq_refl eq_refl).
  all: litmods.
  all: rewrite ?(Z.mod_small (Z.shiftr W 5)) by (clear - RW; split; [apply Z.shiftr_nonneg; lia | rewrite Z.shiftr_div_pow2 by lia; apply Z.div_lt_upper_bound; lia]).
  all: rewrite ?shiftr_shiftr_5_1 by (clear - RW; lia).
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: try (assert (RW6 : 0 <= Z.shiftr W 6 <= 47) by (clear - RW; rewrite Z.shiftr_div_pow2 by lia;
              split; [apply Z.div_pos; lia | assert (W / 2^6 < 48) by (apply Z.div_lt_upper_bound; lia); lia]);
            clear - RW6; lia).
  all: idtac "KREMAINING". all: match goal with |- ?g => idtac g end.
Qed.



Definition callee_regs : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.

Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

#[using="Type"] Lemma efa1_post_of : forall regs R G idx n ctr W mem sz h3 h16 sres,
  regs_ok (efa_env regs G idx n ctr W mem sz h3 h16) sres R ->
  (forall k, In k callee_regs -> sr_get sres (Z_to_bv 5 (Z.of_nat k)) = EVar k) ->
  forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs R G idx n ctr W mem sz h3 h16 sres HR Hs k Hk. rewrite (HR _), (Hs k Hk). cbn [edenot ev efa_env]. unfold reg_ev.
  replace (Nat.ltb k 32) with true by (symmetry; apply Nat.ltb_lt; cbn [callee_regs In] in Hk; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition efa1_post (R regs : bvmap 5 word) (G idx n ctr mem sz h3 h16 : Z) : Prop :=
  getr R 10 = wa G /\ getr R 11 = wa idx /\ getr R 12 = wa n /\ getr R 14 = wa (16 * sz) /\
  getr R 15 = wa (mem + 16 * sz * idx + 16) /\ getr R 16 = wa mem /\ getr R 17 = wa (ef_off0 ctr h3 h16) /\
  getr R 5 = wa (16 * sz - n - 4) /\ getr R 6 = wa (ef_slack sz n) /\
  (forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).

#[using="Type"] Theorem efa1_arm : forall regs m rom G idx n ctr W mem sz h3 h16, efa_pre regs m G idx n ctr W mem sz h3 h16 ->
  exists R, msteps SEGS (mkst regs (wa 0x5494c) m rom) (mkst R (wa 0x549c8) m rom)
         /\ efa1_post R regs G idx n ctr mem sz h3 h16.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n ctr W mem sz h3 h16 P.
  pose proof (efa_regs_ok regs m G idx n ctr W mem sz h3 h16 P) as HR.
  pose proof (efa_know_ok regs m G idx n ctr W mem sz h3 h16 P) as HK.
  set (E := efa_env regs G idx n ctr W mem sz h3 h16) in *.
  pose proof P as P'. destruct P' as [R10 R11 R12 R13 RG AG Ridx Rn Rctr RW Rmem Rsz Rh3 Rh16 RSLOT MW Mmem Msz M12 M13 M14 Fit].
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = ctr) by exact (u_wa_small _ (rng64 _ _ _ Rctr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = h16) by exact (u_wa_small _ (rng64 _ _ _ Rh16 eq_refl)).
  destruct (Z.eq_dec h3 0) as [H0|H0].
  - assert (Hsc : scs_denot SEGS m E (snd (fst RES_efa1_T))).
    { cbn [RES_efa1_T fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      all: apply sc_br_z; cbn [zeval edenot]; rewrite ?Z39, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl); litmods;
           rewrite ?br_eq_z; litmods; first [apply Z.eqb_eq | apply Z.eqb_neq]; rewrite ?Z.mod_small by lia; lia. }
    destruct (run_sound SEGS 200 [0x549c8] scr_efa1_T 0x5494c sr_efa1 kn_efa1 41 _ _ _ E m rom regs RES_efa1_T_ok HR HK Hsc) as (R & HR' & _ & Hms).
    exists R. split; [cbn [RES_efa1_T fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
    cbn [RES_efa1_T fst snd s_regs] in HR'.
    unfold efa1_post. repeat split.
    all: try (apply (efa1_post_of regs R G idx n ctr W mem sz h3 h16 _ HR'); intros k Hk; cbn [callee_regs In] in Hk;
              repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk).
    all: srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z37, ?Z38, ?Z39, ?Z40;
         rewrite ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rh16 eq_refl eq_refl);
         litmods; unfold ef_off0, ef_slack; rewrite ?(proj2 (Z.eqb_eq h3 0) H0);
         rewrite ?(Z.mod_small (-1 * n + 16 * sz + -4)) by (clear - Fit Rn Rsz; lia);
         first [ reflexivity | ring | (f_equal; ring) | (f_equal; f_equal; ring) ].
  - assert (Hsc : scs_denot SEGS m E (snd (fst RES_efa1_F))).
    { cbn [RES_efa1_F fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      all: apply sc_br_z; cbn [zeval edenot]; rewrite ?Z39, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl); litmods;
           rewrite ?br_eq_z; litmods; first [apply Z.eqb_eq | apply Z.eqb_neq]; rewrite ?Z.mod_small by lia; lia. }
    destruct (run_sound SEGS 200 [0x549c8] scr_efa1_F 0x5494c sr_efa1 kn_efa1 41 _ _ _ E m rom regs RES_efa1_F_ok HR HK Hsc) as (R & HR' & _ & Hms).
    exists R. split; [cbn [RES_efa1_F fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
    cbn [RES_efa1_F fst snd s_regs] in HR'.
    unfold efa1_post. repeat split.
    all: try (apply (efa1_post_of regs R G idx n ctr W mem sz h3 h16 _ HR'); intros k Hk; cbn [callee_regs In] in Hk;
              repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk).
    all: srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z37, ?Z38, ?Z39, ?Z40;
         rewrite ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rh16 eq_refl eq_refl);
         litmods; unfold ef_off0, ef_slack; rewrite ?(proj2 (Z.eqb_neq h3 0) H0);
         rewrite ?(Z.mod_small (-1 * n + 16 * sz + -4)) by (clear - Fit Rn Rsz; lia);
         rewrite ?(Z.mod_small (h16 + 1)) by (clear - Rh16; lia);
         first [ reflexivity | ring | (f_equal; ring) | (f_equal; f_equal; ring) ].
Qed.

End EFA.
End AXF_efa1z.


Module AXF_efa2z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma edenot_sltu : forall E a b, edenot E (EAlu ALU_SLTU a b) = wa (if zeval E a mod 2^64 <? zeval E b mod 2^64 then 1 else 0).
Proof.
  intros E a b. cbn [edenot]. rewrite alu_sltu. unfold v_sltu, c_ltu. rewrite !zeval_sound. unfold bv_ltu. rewrite !u_wa.
  destruct (zeval E a mod 2^64 <? zeval E b mod 2^64); reflexivity.
Qed.

Lemma lor_lt_pow : forall a f k, 0 < k -> 0 <= a < 2^k -> 0 <= f < 2^k -> 0 <= Z.lor a f < 2^k.
Proof.
  intros a f k Hk Ha Hf. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a f) 0) as [->|Hnz]; [lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; [destruct (Z.eq_dec a 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]
                       | destruct (Z.eq_dec f 0) as [->|]; [simpl; lia | apply Z.log2_lt_pow2; lia]].
Qed.

Lemma shiftr_lt_pow : forall a k s, 0 <= s -> 0 <= a < 2^k -> 0 <= Z.shiftr a s < 2^k.
Proof.
  intros a k s Hs Ha. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply (Z.le_lt_trans _ a); [apply Z.div_le_upper_bound; [lia|] | lia].
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) Hs). nia.
Qed.

Lemma land_lt_pow : forall a b k, 0 < k -> 0 <= a < 2^k -> 0 <= b -> 0 <= Z.land a b < 2^k.
Proof.
  intros a b k Hk Ha Hb. split; [apply Z.land_nonneg; lia|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]; [lia|].
  apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia. pose proof (Z.log2_land a b ltac:(lia) ltac:(lia)) as L.
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.land_0_l in Hnz; lia|].
  pose proof (Z.log2_lt_pow2 a k ltac:(lia)) as L2. assert (Z.log2 a < k) by (apply L2; lia). lia.
Qed.

(* [comment removed for export] *)
Ltac bnd17 :=
  lazymatch goal with
  | |- 0 <= Z.lor ?a ?b < 2^17 => apply lor_lt_pow; [lia | bnd17 | bnd17]
  | |- 0 <= Z.shiftr ?a ?s < 2^17 => apply shiftr_lt_pow; [lia | bnd17]
  | |- 0 <= Z.land ?a ?b < 2^17 => apply land_lt_pow; [lia | bnd17 | (apply Z.lor_nonneg || apply Z.shiftr_nonneg || lia); try lia]
  | |- _ => lia
  end.

Ltac mod_in :=
  repeat match goal with
  | |- context [ (?x mod 2^64) ] =>
      lazymatch x with context [ _ mod 2^64 ] => fail | _ => idtac end;
      rewrite (Z.mod_small x (2^64)) by (assert (0 <= x < 2^17) by bnd17; lia)
  end.

(* [comment removed for export] *)
Lemma mmask_eq : forall t0 sl, 0 <= t0 -> sl = Z.shiftr t0 4 ->
  Z.lor (Z.shiftr (Z.lor (Z.shiftr (Z.lor sl (Z.shiftr t0 5)) 2) (Z.lor sl (Z.shiftr t0 5))) 4)
        (Z.lor (Z.shiftr (Z.lor sl (Z.shiftr t0 5)) 2) (Z.lor sl (Z.shiftr t0 5))) = ef_mask sl.
Proof.
  intros t0 sl Ht0 ->. unfold ef_mask.
  replace (Z.shiftr t0 5) with (Z.shiftr (Z.shiftr t0 4) 1) by (rewrite Z.shiftr_shiftr by lia; reflexivity).
  rewrite (Z.lor_comm (Z.shiftr (Z.lor (Z.shiftr t0 4) (Z.shiftr (Z.shiftr t0 4) 1)) 2)).
  rewrite (Z.lor_comm (Z.shiftr (Z.lor (Z.lor (Z.shiftr t0 4) (Z.shiftr (Z.shiftr t0 4) 1)) (Z.shiftr (Z.lor (Z.shiftr t0 4) (Z.shiftr (Z.shiftr t0 4) 1)) 2)) 4)).
  reflexivity.
Qed.

Lemma ef_mask_ge : forall sl, 0 <= sl < 256 -> sl <= ef_mask sl /\ 0 <= ef_mask sl <= 2 * sl + 1.
Proof.
  intros sl Hsl.
  assert (C : forallb (fun x => (x <=? ef_mask x) && (0 <=? ef_mask x) && (ef_mask x <=? 2 * x + 1)) (zseq 0 256) = true) by (vm_compute; reflexivity).
  apply forallb_zseq_iff with (x := sl) in C; [|lia]. apply andb_prop in C as (C & C3). apply andb_prop in C as (C1 & C2).
  apply Z.leb_le in C1, C2, C3. lia.
Qed.

Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land (2^64 - 1) x = x.
Proof. intros x Hx. change (2^64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small; lia. Qed.

(* [comment removed for export] *)
Definition mval (sl off0 : Z) : Z :=
  bv_swrap 32 (Z.land ((-1 * ((if sl <? Z.land off0 (ef_mask sl) then 1 else 0) mod 2^64)) mod 2^64) ((-1 * sl + -1) mod 2^64)
               + Z.land off0 (ef_mask sl)).

Lemma land_le_r_Z : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b Ha Hb. rewrite <- (Z2N.id a Ha), <- (Z2N.id b Hb). rewrite <- N2Z.inj_land. split; [apply N2Z.is_nonneg|].
  apply N2Z.inj_le. apply N.land_le_r.
Qed.

Lemma land_le_l_Z : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= a.
Proof. intros a b Ha Hb. rewrite Z.land_comm. apply land_le_r_Z; assumption. Qed.

Lemma masked_val : forall sl off0, 0 <= sl <= 8191 -> 0 <= off0 <= 255 -> sl < off0 -> mval sl off0 = ef_off sl off0.
Proof.
  intros sl off0 Hsl Hoff C. unfold mval, ef_off.
  replace (off0 <=? sl) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta.
  assert (L : 0 <= Z.land off0 (ef_mask sl) <= 255).
  { pose proof (ef_mask_ge sl ltac:(lia)) as (M1 & M2). pose proof (land_le_l_Z off0 (ef_mask sl) ltac:(lia) ltac:(lia)). lia. }
  set (Lv := Z.land off0 (ef_mask sl)) in *.
  destruct (sl <? Lv) eqn:E.
  - apply Z.ltb_lt in E. change ((-1 * (1 mod 2^64)) mod 2^64) with (2^64 - 1).
    replace ((-1 * sl + -1) mod 2^64) with (2^64 - sl - 1) by (apply (Z.mod_unique_pos _ _ (-1)); lia).
    rewrite land_ones64 by lia.
    rewrite swrap32_eq_mod.
    replace ((2 ^ 64 - sl - 1 + Lv) mod 2 ^ 32) with (Lv - (sl + 1)) by (apply (Z.mod_unique_pos _ _ (2^32)); lia).
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
    change (4294967296 `div` 2) with 2147483648. rewrite (Z.mod_small (Lv - (sl + 1) + 2147483648)) by lia. lia.
  - change ((-1 * (0 mod 2^64)) mod 2^64) with 0. rewrite Z.land_0_l, Z.add_0_l.
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
    change (4294967296 `div` 2) with 2147483648. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mval_le : forall sl off0, 0 <= sl <= 8191 -> 0 <= off0 <= 255 -> sl < off0 -> 0 <= mval sl off0 <= sl.
Proof.
  intros sl off0 Hsl Hoff C. rewrite masked_val by lia. unfold ef_off.
  replace (off0 <=? sl) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta.
  pose proof (ef_mask_ge sl ltac:(lia)) as (M1 & M2). pose proof (land_le_r_Z off0 (ef_mask sl) ltac:(lia) ltac:(lia)) as L.
  destruct (sl <? Z.land off0 (ef_mask sl)) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma land_mask_rng : forall sl off0, 0 <= sl <= 255 -> 0 <= off0 <= 255 -> 0 <= Z.land off0 (ef_mask sl) <= 255.
Proof.
  intros sl off0 Hsl Hoff. pose proof (ef_mask_ge sl ltac:(lia)) as (M1 & M2). pose proof (land_le_l_Z off0 (ef_mask sl) ltac:(lia) ltac:(lia)). lia.
Qed.

Record efa2_pre (regs : bvmap 5 word) (t0 sl off0 : Z) : Prop := {
  eb2_R5 : getr regs 5 = wa t0 ; eb2_R6 : getr regs 6 = wa sl ; eb2_R17 : getr regs 17 = wa off0 ;
  eb2_Rt0 : 0 <= t0 <= 131071 ; eb2_Rsl : sl = Z.shiftr t0 4 ; eb2_Roff0 : 0 <= off0 <= 255
}.

Section EFA2.
Context {fx : FPState}.

Definition efa2_env (regs : bvmap 5 word) (t0 sl off0 : Z) : env :=
  Env (reg_ev regs (fun k => wa (nth (k - 32) [t0; sl; off0] 0))) (fun _ => []).

#[using="Type"] Lemma efa2_regs_ok : forall regs t0 sl off0, efa2_pre regs t0 sl off0 -> regs_ok (efa2_env regs t0 sl off0) sr_efa2 regs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs t0 sl off0 P.
  apply (regs_ok_pin _ _ regs 17); [apply (regs_ok_pin _ _ regs 6); [apply (regs_ok_pin _ sr_id regs 5); [apply regs_ok_id|] |] |].
  - rewrite (eb2_R5 _ _ _ _ P). reflexivity.
  - rewrite (eb2_R6 _ _ _ _ P). reflexivity.
  - rewrite (eb2_R17 _ _ _ _ P). reflexivity.
Qed.

#[using="Type"] Lemma efa2_know_ok : forall regs m t0 sl off0, efa2_pre regs t0 sl off0 -> know_ok SEGS (efa2_env regs t0 sl off0) m kn_efa2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m t0 sl off0 P. destruct P as [R5 R6 R17 Rt0 Rsl Roff0].
  assert (Rsl' : 0 <= sl <= 8191) by (subst sl; assert (0 <= Z.shiftr t0 4 < 2^17) by bnd17; rewrite Z.shiftr_div_pow2 by lia;
    split; [apply Z.div_pos; lia | assert (t0 / 2^4 < 8192) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (Z32 : bv_unsigned (ev (efa2_env regs t0 sl off0) 32) = t0) by exact (u_wa_small _ (rng64 _ _ _ Rt0 eq_refl)).
  assert (Z33 : bv_unsigned (ev (efa2_env regs t0 sl off0) 33) = sl) by exact (u_wa_small _ (rng64 _ _ _ Rsl' eq_refl)).
  assert (Z34 : bv_unsigned (ev (efa2_env regs t0 sl off0) 34) = off0) by exact (u_wa_small _ (rng64 _ _ _ Roff0 eq_refl)).
  unfold know_ok, kn_efa2. repeat (first [apply Forall_nil | apply Forall_cons]).
  all: (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end); cbn [zeval edenot e_t0 e_sl e_off0]; rewrite ?Z32, ?Z33, ?Z34;
       rewrite ?(mod64_of_range _ _ _ Rt0 eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsl' eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff0 eq_refl eq_refl); lia.
Qed.



Definition efa2_keep : list nat := [1;2;3;4;8;9;10;11;12;14;15;16;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%nat.

Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

#[using="Type"] Lemma efa2_post_of : forall regs R t0 sl off0 sres,
  regs_ok (efa2_env regs t0 sl off0) sres R ->
  (forall k, In k efa2_keep -> sr_get sres (Z_to_bv 5 (Z.of_nat k)) = EVar k) ->
  forall k, In k efa2_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs R t0 sl off0 sres HR Hs k Hk. rewrite (HR _), (Hs k Hk). cbn [edenot ev efa2_env]. unfold reg_ev.
  replace (Nat.ltb k 32) with true by (symmetry; apply Nat.ltb_lt; cbn [efa2_keep In] in Hk; lia). reflexivity.
Qed.

#[using="Type"] Theorem efa2_arm : forall regs m rom t0 sl off0, efa2_pre regs t0 sl off0 ->
  exists R, msteps SEGS (mkst regs (wa 0x549c8) m rom) (mkst R (wa 0x54a04) m rom)
         /\ getr R 17 = wa (ef_off sl off0)
         /\ (forall k, In k efa2_keep -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom t0 sl off0 P.
  pose proof (efa2_regs_ok regs t0 sl off0 P) as HR. pose proof (efa2_know_ok regs m t0 sl off0 P) as HK.
  set (E := efa2_env regs t0 sl off0) in *.
  pose proof P as P'. destruct P' as [R5 R6 R17 Rt0 Rsl Roff0].
  assert (Rsl' : 0 <= sl <= 8191) by (subst sl; rewrite Z.shiftr_div_pow2 by lia;
    split; [apply Z.div_pos; lia | assert (t0 / 2^4 < 8192) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (Z32 : bv_unsigned (ev E 32) = t0) by exact (u_wa_small _ (rng64 _ _ _ Rt0 eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = sl) by exact (u_wa_small _ (rng64 _ _ _ Rsl' eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = off0) by exact (u_wa_small _ (rng64 _ _ _ Roff0 eq_refl)).
  destruct (Z_lt_le_dec sl off0) as [C|C].
  - assert (L : 0 <= Z.land off0 (ef_mask sl) <= 255) by (apply land_mask_rng; lia).
    pose proof (mval_le sl off0 Rsl' Roff0 C) as ML.
    assert (Hsc : scs_denot SEGS m E (snd (fst RES_efa2_FT))).
    { cbn [RES_efa2_FT fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      all: apply sc_br_z; cbn [zeval]; rewrite ?edenot_sltu, ?u_wa; cbn [zeval edenot]; rewrite ?Z32, ?Z33, ?Z34.
      all: rewrite ?(mod64_of_range _ _ _ Rt0 eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsl' eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff0 eq_refl eq_refl).
      all: litmods; mod_in; rewrite ?br_geu_z; rewrite ?(mmask_eq t0 sl ltac:(lia) Rsl).
      all: rewrite ?(Z.mod_small (Z.land off0 (ef_mask sl)) (2^64)) by lia.
      all: fold (mval sl off0).
      all: rewrite ?(Z.mod_small (mval sl off0) (2^64)) by lia.
      all: rewrite ?(mod64_of_range _ _ _ Rsl' eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff0 eq_refl eq_refl).
      all: first [ apply negb_true_iff, Z.ltb_ge; lia | apply negb_false_iff, Z.ltb_lt; lia ]. }
    destruct (run_sound SEGS 100 [0x54a04] scr_efa2_FT 0x549c8 sr_efa2 kn_efa2 35 _ _ _ E m rom regs RES_efa2_FT_ok HR HK Hsc) as (R & HR' & _ & Hms).
    exists R. split; [cbn [RES_efa2_FT fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
    cbn [RES_efa2_FT fst snd s_regs] in HR'. split.
    + srg HR'. rewrite zeval_sound. f_equal. cbn [zeval]. rewrite ?edenot_sltu, ?u_wa. cbn [zeval edenot]. rewrite ?Z32, ?Z33, ?Z34.
      rewrite ?(mod64_of_range _ _ _ Rt0 eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsl' eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff0 eq_refl eq_refl).
      litmods. mod_in. rewrite ?(mmask_eq t0 sl ltac:(lia) Rsl).
      rewrite ?(Z.mod_small (Z.land off0 (ef_mask sl)) (2^64)) by lia.
      fold (mval sl off0). apply masked_val; lia.
    + apply (efa2_post_of regs R t0 sl off0 _ HR'); intros k Hk; cbn [efa2_keep In] in Hk;
        repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk.
  - assert (Hsc : scs_denot SEGS m E (snd (fst RES_efa2_T))).
    { cbn [RES_efa2_T fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      all: apply sc_br_z; cbn [zeval edenot]; rewrite ?Z33, ?Z34.
      all: rewrite ?br_geu_z, ?(mod64_of_range _ _ _ Rsl' eq_refl eq_refl), ?(mod64_of_range _ _ _ Roff0 eq_refl eq_refl).
      all: first [ apply negb_true_iff, Z.ltb_ge; lia | apply negb_false_iff, Z.ltb_lt; lia ]. }
    destruct (run_sound SEGS 100 [0x54a04] scr_efa2_T 0x549c8 sr_efa2 kn_efa2 35 _ _ _ E m rom regs RES_efa2_T_ok HR HK Hsc) as (R & HR' & _ & Hms).
    exists R. split; [cbn [RES_efa2_T fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
    cbn [RES_efa2_T fst snd s_regs] in HR'. split.
    + srg HR'. rewrite zeval_sound. f_equal. cbn [zeval edenot]. rewrite ?Z34.
      rewrite ?(mod64_of_range _ _ _ Roff0 eq_refl eq_refl). unfold ef_off. replace (off0 <=? sl) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    + apply (efa2_post_of regs R t0 sl off0 _ HR'); intros k Hk; cbn [efa2_keep In] in Hk;
        repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk.
Qed.

End EFA2.
End AXF_efa2z.

From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.

Module AXF_efa1m.
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
Definition e_idx := EVar 33.
Definition e_n := EVar 34.
Definition e_ctr := EVar 35.
Definition e_W := EVar 36.
Definition e_mem := EVar 37.
Definition e_sz := EVar 38.
Definition e_h3 := EVar 39.
Definition e_h16 := EVar 40.
Definition TABSZ := EAlu ALU_AND (EAlu ALU_SRL e_W (ELit 5)) (ELit 126).
Definition SLOT := EAlu ALU_ADD e_mem (EMd M_MUL (EMd M_MUL (ELit 16) e_sz) e_idx).
Definition sr_efa1m := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G)) 11 (e_idx)) 12 (e_n)) 13 (e_ctr)).
Definition kn_efa1m : list kentry :=
  [ KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_n 1 131051;
    KRange e_ctr 0 (2^64-1);
    KRange e_W 4096 (2^63-1);
    KRange e_mem 1 (2^63-1);
    KRange e_sz 1 8191;
    KRange e_h3 0 255;
    KRange e_h16 0 65535;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 16) 8 e_mem;
    KWord (SA TABSZ 98984) 2 e_sz;
    KRange SLOT 1 (2^63-1);
    KWord (SA SLOT 12) 1 (ELit 0);
    KWord (SA SLOT 13) 1 e_h3;
    KWord (SA SLOT 14) 2 e_h16 ].
Definition scr_efa1m : scripts := SCR [true] [] [].
Definition ss_efa1m := SS 0x5494c sr_efa1m [] kn_efa1m 41.
Definition RUN_efa1m := sym_exec SEGS 200 true [0x549c8] scr_efa1m ss_efa1m [].

Definition scr_efa1m_TT : scripts := SCR [true; true] [] [].
Definition RES_efa1m_TT := Eval vm_compute in sym_exec SEGS 200 true [0x549c8] scr_efa1m_TT ss_efa1m [].
Lemma RES_efa1m_TT_ok : sym_exec SEGS 200 true [0x549c8] scr_efa1m_TT (SS 0x5494c sr_efa1m [] kn_efa1m 41) [] = RES_efa1m_TT.
Proof. vm_compute. reflexivity. Qed.

Definition scr_efa1m_TF : scripts := SCR [true; false] [] [].
Definition RES_efa1m_TF := Eval vm_compute in sym_exec SEGS 200 true [0x549c8] scr_efa1m_TF ss_efa1m [].
Lemma RES_efa1m_TF_ok : sym_exec SEGS 200 true [0x549c8] scr_efa1m_TF (SS 0x5494c sr_efa1m [] kn_efa1m 41) [] = RES_efa1m_TF.
Proof. vm_compute. reflexivity. Qed.
End AXF_efa1m.


Module AXF_efa1mz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1m.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record efa1m_pre (regs : bvmap 5 word) (m : word -> option byte) (G idx n ctr W mem sz h3 h16 : Z) : Prop := {
  em_R10 : getr regs 10 = wa G ; em_R11 : getr regs 11 = wa idx ; em_R12 : getr regs 12 = wa n ; em_R13 : getr regs 13 = wa ctr ;
  em_RG : 1 <= G <= 2^63-1 ; em_AG : G mod 8 = 0 ; em_Ridx : 0 <= idx <= 31 ; em_Rn : 1 <= n <= 131051 ;
  em_Rctr : 0 <= ctr <= 2^64-1 ; em_RW : 4096 <= W <= 2^63-1 ; em_Wl : Z.land W 31 <> 0 ; em_Rmem : 1 <= mem <= 2^63-1 ; em_Rsz : 1 <= sz <= 8191 ;
  em_Rh3 : 0 <= h3 <= 255 ; em_Rh16 : 0 <= h16 <= 65535 ;
  em_RSLOT : 1 <= mem + 16 * sz * idx <= 2^63-1 ;
  em_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  em_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa mem)) ;
  em_Msz : rdn SEGS m (wa (Z.land (Z.shiftr W 5) 126 + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz)) ;
  em_M12 : rdn SEGS m (wa (mem + 16 * sz * idx + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  em_M13 : rdn SEGS m (wa (mem + 16 * sz * idx + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  em_M14 : rdn SEGS m (wa (mem + 16 * sz * idx + 14)) 2 = Some (word_to_le_bytes 2 (wa h16)) ;
  em_fit : n + 4 <= 16 * sz
}.

Lemma land126 : forall W, 0 <= W -> 0 <= Z.land (Z.shiftr W 5) 126 <= 126.
Proof.
  intros W HW. assert (H0 : 0 <= Z.shiftr W 5) by (apply Z.shiftr_nonneg; lia).
  rewrite <- (Z2N.id _ H0). change 126 with (Z.of_N 126). rewrite <- N2Z.inj_land. split; [apply N2Z.is_nonneg|].
  apply N2Z.inj_le. apply N.land_le_r.
Qed.

Section EFA1M.
Context {fx : FPState}.

Definition efa1m_env (regs : bvmap 5 word) (G idx n ctr W mem sz h3 h16 : Z) : env :=
  Env (reg_ev regs (fun k => wa (nth (k - 32) [G; idx; n; ctr; W; mem; sz; h3; h16] 0))) (fun _ => []).

#[using="Type"] Lemma efa1m_regs_ok : forall regs m G idx n ctr W mem sz h3 h16, efa1m_pre regs m G idx n ctr W mem sz h3 h16 ->
  regs_ok (efa1m_env regs G idx n ctr W mem sz h3 h16) sr_efa1m regs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx n ctr W mem sz h3 h16 P.
  apply (regs_ok_pin _ _ regs 13); [apply (regs_ok_pin _ _ regs 12); [apply (regs_ok_pin _ _ regs 11);
    [apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|] |] |] |].
  - rewrite (em_R10 _ _ _ _ _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (em_R11 _ _ _ _ _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (em_R12 _ _ _ _ _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (em_R13 _ _ _ _ _ _ _ _ _ _ _ P). reflexivity.
Qed.

#[using="Type"] Lemma efa1m_know_ok : forall regs m G idx n ctr W mem sz h3 h16, efa1m_pre regs m G idx n ctr W mem sz h3 h16 ->
  know_ok SEGS (efa1m_env regs G idx n ctr W mem sz h3 h16) m kn_efa1m.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx n ctr W mem sz h3 h16 P.
  destruct P as [R10 R11 R12 R13 RG AG Ridx Rn Rctr RW Wl Rmem Rsz Rh3 Rh16 RSLOT MW Mmem Msz M12 M13 M14 Fit].
  set (E := efa1m_env regs G idx n ctr W mem sz h3 h16).
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = ctr) by exact (u_wa_small _ (rng64 _ _ _ Rctr eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = h16) by exact (u_wa_small _ (rng64 _ _ _ Rh16 eq_refl)).
  unfold know_ok, kn_efa1m.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) ].
  all: cbn [zeval edenot e_G e_idx e_n e_ctr e_W e_mem e_sz e_h3 e_h16 TABSZ SLOT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
  all: rewrite ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl),
         ?(mod64_of_range _ _ _ RW eq_refl eq_refl), ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rh16 eq_refl eq_refl), ?(mod64_of_range _ _ _ RSLOT eq_refl eq_refl).
  all: litmods.
  all: rewrite ?(Z.mod_small (Z.shiftr W 5)) by (clear - RW; split; [apply Z.shiftr_nonneg; lia | rewrite Z.shiftr_div_pow2 by lia; apply Z.div_lt_upper_bound; lia]).
  all: rewrite ?shiftr_shiftr_5_1 by (clear - RW; lia).
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: try (assert (RW6 : 0 <= Z.shiftr W 6 <= 47) by (clear - RW; rewrite Z.shiftr_div_pow2 by lia;
              split; [apply Z.div_pos; lia | assert (W / 2^6 < 48) by (apply Z.div_lt_upper_bound; lia); lia]);
            clear - RW6; lia).
  all: pose proof (land126 W ltac:(lia)); lia.
Qed.



Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

#[using="Type"] Lemma efa1m_post_of : forall regs R G idx n ctr W mem sz h3 h16 sres,
  regs_ok (efa1m_env regs G idx n ctr W mem sz h3 h16) sres R ->
  (forall k, In k callee_regs -> sr_get sres (Z_to_bv 5 (Z.of_nat k)) = EVar k) ->
  forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs R G idx n ctr W mem sz h3 h16 sres HR Hs k Hk. rewrite (HR _), (Hs k Hk). cbn [edenot ev efa1m_env]. unfold reg_ev.
  replace (Nat.ltb k 32) with true by (symmetry; apply Nat.ltb_lt; cbn [callee_regs In] in Hk; lia). reflexivity.
Qed.

#[using="Type"] Theorem efa1m_arm : forall regs m rom G idx n ctr W mem sz h3 h16, efa1m_pre regs m G idx n ctr W mem sz h3 h16 ->
  exists R, msteps SEGS (mkst regs (wa 0x5494c) m rom) (mkst R (wa 0x549c8) m rom)
         /\ efa1_post R regs G idx n ctr mem sz h3 h16.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n ctr W mem sz h3 h16 P.
  pose proof (efa1m_regs_ok regs m G idx n ctr W mem sz h3 h16 P) as HR.
  pose proof (efa1m_know_ok regs m G idx n ctr W mem sz h3 h16 P) as HK.
  set (E := efa1m_env regs G idx n ctr W mem sz h3 h16) in *.
  pose proof P as P'. destruct P' as [R10 R11 R12 R13 RG AG Ridx Rn Rctr RW Wl Rmem Rsz Rh3 Rh16 RSLOT MW Mmem Msz M12 M13 M14 Fit].
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = ctr) by exact (u_wa_small _ (rng64 _ _ _ Rctr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = sz) by exact (u_wa_small _ (rng64 _ _ _ Rsz eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = h16) by exact (u_wa_small _ (rng64 _ _ _ Rh16 eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  destruct (Z.eq_dec h3 0) as [H0|H0].
  - assert (Hsc : scs_denot SEGS m E (snd (fst RES_efa1m_TT))).
    { cbn [RES_efa1m_TT fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      all: apply sc_br_z; cbn [zeval edenot]; rewrite ?Z36, ?Z39, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl); litmods;
           rewrite ?br_eq_z, ?br_ne_z; litmods; rewrite ?Z36, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl); pose proof (land31_bound W ltac:(lia));
           rewrite ?(Z.mod_small (Z.land W 31)) by lia;
           first [apply Z.eqb_eq | apply Z.eqb_neq | apply negb_true_iff, Z.eqb_neq | apply negb_false_iff, Z.eqb_eq]; rewrite ?Z.mod_small by lia; lia. }
    destruct (run_sound SEGS 200 [0x549c8] scr_efa1m_TT 0x5494c sr_efa1m kn_efa1m 41 _ _ _ E m rom regs RES_efa1m_TT_ok HR HK Hsc) as (R & HR' & _ & Hms).
    exists R. split; [cbn [RES_efa1m_TT fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
    cbn [RES_efa1m_TT fst snd s_regs] in HR'.
    unfold efa1_post. repeat split.
    all: try (apply (efa1m_post_of regs R G idx n ctr W mem sz h3 h16 _ HR'); intros k Hk; cbn [callee_regs In] in Hk;
              repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk).
    all: srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z37, ?Z38, ?Z39, ?Z40;
         rewrite ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rh16 eq_refl eq_refl);
         litmods; unfold ef_off0, ef_slack; rewrite ?(proj2 (Z.eqb_eq h3 0) H0);
         rewrite ?(Z.mod_small (-1 * n + 16 * sz + -4)) by (clear - Fit Rn Rsz; lia);
         first [ reflexivity | ring | (f_equal; ring) | (f_equal; f_equal; ring) ].
  - assert (Hsc : scs_denot SEGS m E (snd (fst RES_efa1m_TF))).
    { cbn [RES_efa1m_TF fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      all: apply sc_br_z; cbn [zeval edenot]; rewrite ?Z36, ?Z39, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl); litmods;
           rewrite ?br_eq_z, ?br_ne_z; litmods; rewrite ?Z36, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl); pose proof (land31_bound W ltac:(lia));
           rewrite ?(Z.mod_small (Z.land W 31)) by lia;
           first [apply Z.eqb_eq | apply Z.eqb_neq | apply negb_true_iff, Z.eqb_neq | apply negb_false_iff, Z.eqb_eq]; rewrite ?Z.mod_small by lia; lia. }
    destruct (run_sound SEGS 200 [0x549c8] scr_efa1m_TF 0x5494c sr_efa1m kn_efa1m 41 _ _ _ E m rom regs RES_efa1m_TF_ok HR HK Hsc) as (R & HR' & _ & Hms).
    exists R. split; [cbn [RES_efa1m_TF fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
    cbn [RES_efa1m_TF fst snd s_regs] in HR'.
    unfold efa1_post. repeat split.
    all: try (apply (efa1m_post_of regs R G idx n ctr W mem sz h3 h16 _ HR'); intros k Hk; cbn [callee_regs In] in Hk;
              repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk).
    all: srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z37, ?Z38, ?Z39, ?Z40;
         rewrite ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Rsz eq_refl eq_refl), ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rh16 eq_refl eq_refl);
         litmods; unfold ef_off0, ef_slack; rewrite ?(proj2 (Z.eqb_neq h3 0) H0);
         rewrite ?(Z.mod_small (-1 * n + 16 * sz + -4)) by (clear - Fit Rn Rsz; lia);
         rewrite ?(Z.mod_small (h16 + 1)) by (clear - Rh16; lia);
         first [ reflexivity | ring | (f_equal; ring) | (f_equal; f_equal; ring) ].
Qed.

End EFA1M.
End AXF_efa1mz.


Module AXF_efa1d.
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
Definition e_n := EVar 33.
Definition e_ctr := EVar 34.
Definition e_W := EVar 35.
Definition e_mem := EVar 36.
Definition e_h3 := EVar 37.
Definition e_h16 := EVar 38.
Definition sr_efa1d := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G)) 11 (ELit 0)) 12 (e_n)) 13 (e_ctr)).
Definition kn_efa1d : list kentry :=
  [ KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_n 1 (2^26);
    KRange e_ctr 0 (2^64-1);
    KRange e_W 4096 (2^63-1);
    KRange e_mem 1 (2^63-1);
    KRange e_h3 0 255;
    KRange e_h16 0 65535;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 16) 8 e_mem;
    KWord (SA e_mem 12) 1 (ELit 0);
    KWord (SA e_mem 13) 1 e_h3;
    KWord (SA e_mem 14) 2 e_h16 ].
Definition scr_efa1d : scripts := SCR [false] [] [].
Definition ss_efa1d := SS 0x5494c sr_efa1d [] kn_efa1d 39.
Definition RUN_efa1d := sym_exec SEGS 200 true [0x549c8] scr_efa1d ss_efa1d [].

Definition scr_efa1d_FT : scripts := SCR [false; true] [] [].
Definition RES_efa1d_FT := Eval vm_compute in sym_exec SEGS 200 true [0x549c8] scr_efa1d_FT ss_efa1d [].
Lemma RES_efa1d_FT_ok : sym_exec SEGS 200 true [0x549c8] scr_efa1d_FT (SS 0x5494c sr_efa1d [] kn_efa1d 39) [] = RES_efa1d_FT.
Proof. vm_compute. reflexivity. Qed.

Definition scr_efa1d_FF : scripts := SCR [false; false] [] [].
Definition RES_efa1d_FF := Eval vm_compute in sym_exec SEGS 200 true [0x549c8] scr_efa1d_FF ss_efa1d [].
Lemma RES_efa1d_FF_ok : sym_exec SEGS 200 true [0x549c8] scr_efa1d_FF (SS 0x5494c sr_efa1d [] kn_efa1d 39) [] = RES_efa1d_FF.
Proof. vm_compute. reflexivity. Qed.
End AXF_efa1d.


Module AXF_efa1dz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1d.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition ef_dstride (W : Z) : Z := 4096 * Z.shiftr W 12 - 16.

Record efa1d_pre (regs : bvmap 5 word) (m : word -> option byte) (G n ctr W mem h3 h16 : Z) : Prop := {
  ed_R10 : getr regs 10 = wa G ; ed_R11 : getr regs 11 = wa 0 ; ed_R12 : getr regs 12 = wa n ; ed_R13 : getr regs 13 = wa ctr ;
  ed_RG : 1 <= G <= 2^63-1 ; ed_AG : G mod 8 = 0 ; ed_Rn : 1 <= n <= 2^26 ;
  ed_Rctr : 0 <= ctr <= 2^64-1 ; ed_RW : 4096 <= W <= 2^63-1 ; ed_Wl : Z.land W 31 = 0 ; ed_Rmem : 1 <= mem <= 2^63-1 ;
  ed_Rh3 : 0 <= h3 <= 255 ; ed_Rh16 : 0 <= h16 <= 65535 ;
  ed_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  ed_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa mem)) ;
  ed_M12 : rdn SEGS m (wa (mem + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  ed_M13 : rdn SEGS m (wa (mem + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  ed_M14 : rdn SEGS m (wa (mem + 14)) 2 = Some (word_to_le_bytes 2 (wa h16)) ;
  ed_fit : n + 4 <= ef_dstride W ;
  ed_mend : mem + 16 <= 2^63 - 1
}.

Section EFA1D.
Context {fx : FPState}.

Definition efa1d_env (regs : bvmap 5 word) (G n ctr W mem h3 h16 : Z) : env :=
  Env (reg_ev regs (fun k => wa (nth (k - 32) [G; n; ctr; W; mem; h3; h16] 0))) (fun _ => []).

#[using="Type"] Lemma efa1d_regs_ok : forall regs m G n ctr W mem h3 h16, efa1d_pre regs m G n ctr W mem h3 h16 ->
  regs_ok (efa1d_env regs G n ctr W mem h3 h16) sr_efa1d regs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G n ctr W mem h3 h16 P.
  apply (regs_ok_pin _ _ regs 13); [apply (regs_ok_pin _ _ regs 12); [apply (regs_ok_pin _ _ regs 11);
    [apply (regs_ok_pin _ sr_id regs 10); [apply regs_ok_id|] |] |] |].
  - rewrite (ed_R10 _ _ _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (ed_R11 _ _ _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (ed_R12 _ _ _ _ _ _ _ _ _ P). reflexivity.
  - rewrite (ed_R13 _ _ _ _ _ _ _ _ _ P). reflexivity.
Qed.

#[using="Type"] Lemma efa1d_know_ok : forall regs m G n ctr W mem h3 h16, efa1d_pre regs m G n ctr W mem h3 h16 ->
  know_ok SEGS (efa1d_env regs G n ctr W mem h3 h16) m kn_efa1d.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G n ctr W mem h3 h16 P.
  destruct P as [R10 R11 R12 R13 RG AG Rn Rctr RW Wl Rmem Rh3 Rh16 MW Mmem M12 M13 M14 Fit Mend].
  set (E := efa1d_env regs G n ctr W mem h3 h16).
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = ctr) by exact (u_wa_small _ (rng64 _ _ _ Rctr eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = h16) by exact (u_wa_small _ (rng64 _ _ _ Rh16 eq_refl)).
  unfold know_ok, kn_efa1d.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) ].
  all: cbn [zeval edenot e_G e_n e_ctr e_W e_mem e_h3 e_h16 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38.
  all: rewrite ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rn eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl), ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl),
         ?(mod64_of_range _ _ _ Rh16 eq_refl eq_refl).
  all: litmods.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: try (clear - Mend Rmem; lia).
Qed.

Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

#[using="Type"] Lemma efa1d_post_of : forall regs R G n ctr W mem h3 h16 sres,
  regs_ok (efa1d_env regs G n ctr W mem h3 h16) sres R ->
  (forall k, In k callee_regs -> sr_get sres (Z_to_bv 5 (Z.of_nat k)) = EVar k) ->
  forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs R G n ctr W mem h3 h16 sres HR Hs k Hk. rewrite (HR _), (Hs k Hk). cbn [edenot ev efa1d_env]. unfold reg_ev.
  replace (Nat.ltb k 32) with true by (symmetry; apply Nat.ltb_lt; cbn [callee_regs In] in Hk; lia). reflexivity.
Qed.

#[using="Type"] Lemma dstride_rng : forall W, 4096 <= W <= 2^63-1 -> 1 <= Z.shiftr W 12 <= 2^51 /\ 4096 * Z.shiftr W 12 <= W.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W RW. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
  split; [split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia] | apply Z.mul_div_le; lia].
Qed.

#[using="Type"] Theorem efa1d_arm : forall regs m rom G n ctr W mem h3 h16, efa1d_pre regs m G n ctr W mem h3 h16 ->
  exists R, msteps SEGS (mkst regs (wa 0x5494c) m rom) (mkst R (wa 0x549c8) m rom)
         /\ efa1_post R regs G 0 n ctr mem (256 * Z.shiftr W 12 - 1) h3 h16.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G n ctr W mem h3 h16 P.
  pose proof (efa1d_regs_ok regs m G n ctr W mem h3 h16 P) as HR.
  pose proof (efa1d_know_ok regs m G n ctr W mem h3 h16 P) as HK.
  set (E := efa1d_env regs G n ctr W mem h3 h16) in *.
  pose proof P as P'. destruct P' as [R10 R11 R12 R13 RG AG Rn Rctr RW Wl Rmem Rh3 Rh16 MW Mmem M12 M13 M14 Fit Mend].
  pose proof (dstride_rng W RW) as (ML1 & ML2). unfold ef_dstride in Fit.
  assert (RML : 0 <= Z.shiftr W 12 <= 2^63-1) by lia.
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = n) by exact (u_wa_small _ (rng64 _ _ _ Rn eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = ctr) by exact (u_wa_small _ (rng64 _ _ _ Rctr eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = mem) by exact (u_wa_small _ (rng64 _ _ _ Rmem eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = h3) by exact (u_wa_small _ (rng64 _ _ _ Rh3 eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = h16) by exact (u_wa_small _ (rng64 _ _ _ Rh16 eq_refl)).
  assert (SW : Z.shiftr W 12 mod 2^64 = Z.shiftr W 12) by (apply Z.mod_small; lia).
  destruct (Z.eq_dec h3 0) as [H0|H0].
  - assert (Hsc : scs_denot SEGS m E (snd (fst RES_efa1d_FT))).
    { cbn [RES_efa1d_FT fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      all: apply sc_br_z; cbn [zeval edenot]; rewrite ?Z35, ?Z37, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl); litmods;
           rewrite ?br_eq_z, ?br_ne_z; litmods; rewrite ?Z35, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl);
           pose proof (land31_bound W ltac:(lia));
           rewrite ?(Z.mod_small (Z.land W 31)) by lia;
           first [apply Z.eqb_eq | apply Z.eqb_neq | apply negb_true_iff, Z.eqb_neq | apply negb_false_iff, Z.eqb_eq]; rewrite ?Z.mod_small by lia; lia. }
    destruct (run_sound SEGS 200 [0x549c8] scr_efa1d_FT 0x5494c sr_efa1d kn_efa1d 39 _ _ _ E m rom regs RES_efa1d_FT_ok HR HK Hsc) as (R & HR' & _ & Hms).
    exists R. split; [cbn [RES_efa1d_FT fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
    cbn [RES_efa1d_FT fst snd s_regs] in HR'.
    unfold efa1_post. repeat split.
    all: try (apply (efa1d_post_of regs R G n ctr W mem h3 h16 _ HR'); intros k Hk; cbn [callee_regs In] in Hk;
              repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk).
    all: srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38;
         rewrite ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl), ?(mod64_of_range _ _ _ Rh16 eq_refl eq_refl);
         litmods; rewrite ?SW; unfold ef_off0, ef_slack; rewrite ?(proj2 (Z.eqb_eq h3 0) H0);
         rewrite ?(Z.mod_small (-1 * n + 4096 * Z.shiftr W 12 + -20)) by (clear - Fit Rn ML1 ML2; lia);
         rewrite ?(Z.mod_small (4096 * Z.shiftr W 12 + -16)) by (clear - Fit Rn ML1 ML2 RW; lia);
         rewrite ?(Z.mod_small (mem + 16)) by (clear - Mend Rmem; lia);
         first [ reflexivity | ring | (f_equal; ring) | (f_equal; f_equal; ring) ].
  - assert (Hsc : scs_denot SEGS m E (snd (fst RES_efa1d_FF))).
    { cbn [RES_efa1d_FF fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      all: apply sc_br_z; cbn [zeval edenot]; rewrite ?Z35, ?Z37, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl); litmods;
           rewrite ?br_eq_z, ?br_ne_z; litmods; rewrite ?Z35, ?(mod64_of_range _ _ _ Rh3 eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl);
           pose proof (land31_bound W ltac:(lia));
           rewrite ?(Z.mod_small (Z.land W 31)) by lia;
           first [apply Z.eqb_eq | apply Z.eqb_neq | apply negb_true_iff, Z.eqb_neq | apply negb_false_iff, Z.eqb_eq]; rewrite ?Z.mod_small by lia; lia. }
    destruct (run_sound SEGS 200 [0x549c8] scr_efa1d_FF 0x5494c sr_efa1d kn_efa1d 39 _ _ _ E m rom regs RES_efa1d_FF_ok HR HK Hsc) as (R & HR' & _ & Hms).
    exists R. split; [cbn [RES_efa1d_FF fst snd s_pc s_log mem_denot] in Hms; exact Hms|].
    cbn [RES_efa1d_FF fst snd s_regs] in HR'.
    unfold efa1_post. repeat split.
    all: try (apply (efa1d_post_of regs R G n ctr W mem h3 h16 _ HR'); intros k Hk; cbn [callee_regs In] in Hk;
              repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk).
    all: srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38;
         rewrite ?(mod64_of_range _ _ _ Rn eq_refl eq_refl), ?(mod64_of_range _ _ _ Rctr eq_refl eq_refl),
           ?(mod64_of_range _ _ _ Rmem eq_refl eq_refl), ?(mod64_of_range _ _ _ RW eq_refl eq_refl), ?(mod64_of_range _ _ _ Rh16 eq_refl eq_refl);
         litmods; rewrite ?SW; unfold ef_off0, ef_slack; rewrite ?(proj2 (Z.eqb_neq h3 0) H0);
         rewrite ?(Z.mod_small (-1 * n + 4096 * Z.shiftr W 12 + -20)) by (clear - Fit Rn ML1 ML2; lia);
         rewrite ?(Z.mod_small (4096 * Z.shiftr W 12 + -16)) by (clear - Fit Rn ML1 ML2 RW; lia);
         rewrite ?(Z.mod_small (mem + 16)) by (clear - Mend Rmem; lia);
         rewrite ?(Z.mod_small (h16 + 1)) by (clear - Rh16; lia);
         first [ reflexivity | ring | (f_equal; ring) | (f_equal; f_equal; ring) ].
Qed.

End EFA1D.
End AXF_efa1dz.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_efb OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa2z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1m OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1mz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1d OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efz.AXF_efa1dz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ef_st (mem sz idx : Z) : Z := mem + 16 * sz * idx + 16.
Definition ef_offv (sz n ctr h3 h16 : Z) : Z := ef_off (ef_slack sz n) (ef_off0 ctr h3 h16).

Record ef_pre (regs : bvmap 5 word) (m : word -> option byte) (G idx n ctr W mem sz h3 h16 : Z) : Prop := {
  ef_A : efa_pre regs m G idx n ctr W mem sz h3 h16 ;
  ef_Rend : ef_st mem sz idx + 16 * sz <= 2^63 ;
  ef_W : forall d k, 0 <= d -> d + Z.of_nat k <= 16 * sz -> store_ok SEGS m (wa (ef_st mem sz idx - 4 + d)) k = true ;
  ef_D : G + 16 + 8 <= ef_st mem sz idx - 4 \/ ef_st mem sz idx - 4 + 16 * sz <= G + 16
}.

Lemma ef_offv_rng : forall sz n ctr h3 h16, n + 4 <= 16 * sz -> 16 * sz - n - 4 <= 131071 ->
  0 <= ef_offv sz n ctr h3 h16 <= 255 /\ ef_offv sz n ctr h3 h16 <= ef_slack sz n.
Proof.
  intros sz n ctr h3 h16 Fit Rt0. unfold ef_offv.
  pose proof (land255_range (if h3 =? 0 then ctr else h16 + 1)) as R0. change (Z.land (if h3 =? 0 then ctr else h16 + 1) 255) with (ef_off0 ctr h3 h16) in R0.
  assert (S0 : 0 <= ef_slack sz n <= 8191).
  { unfold ef_slack. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    assert ((16 * sz - n - 4) / 2^4 < 8192) by (apply Z.div_lt_upper_bound; lia). lia. }
  destruct (Z_lt_le_dec (ef_slack sz n) (ef_off0 ctr h3 h16)) as [C|C].
  - pose proof (mval_le _ _ S0 R0 C) as ML. rewrite masked_val in ML by lia. lia.
  - unfold ef_off. replace (ef_off0 ctr h3 h16 <=? ef_slack sz n) with true by (symmetry; apply Z.leb_le; lia). lia.
Qed.

Section EF.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma ef_after_a1 : forall regs R1 m rom G idx n ctr mem sz h3 h16,
  efa1_post R1 regs G idx n ctr mem sz h3 h16 ->
  1 <= G <= 2^63-1 -> G mod 8 = 0 -> 0 <= idx <= 31 -> 1 <= n <= 2^26 -> 1 <= mem <= 2^63-1 -> 1 <= sz <= 2^23 ->
  1 <= mem + 16 * sz * idx <= 2^63-1 -> n + 4 <= 16 * sz -> 16 * sz - n - 4 <= 131071 -> 16 * sz * idx <= 2^30 ->
  rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa mem)) ->
  ef_st mem sz idx + 16 * sz <= 2^63 ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 * sz -> store_ok SEGS m (wa (ef_st mem sz idx - 4 + d)) k = true) ->
  G + 16 + 8 <= ef_st mem sz idx - 4 \/ ef_st mem sz idx - 4 + 16 * sz <= G + 16 ->
  exists R, msteps SEGS (mkst R1 (wa 0x549c8) m rom)
                        (mkst R (wa 0x54a98) (efb_mem m idx n mem sz (ef_st mem sz idx) (ef_offv sz n ctr h3 h16)) rom)
         /\ getr R 10 = wa (ef_st mem sz idx + 16 * ef_offv sz n ctr h3 h16)
         /\ (forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs R1 m rom G idx n ctr mem sz h3 h16 P1 RG AG Ridx Rn Rmem Rsz RSLOT Fit Rt0 Ridx2 Mmem Rend Wok D.
  destruct P1 as (Q10 & Q11 & Q12 & Q14 & Q15 & Q16 & Q17 & Q5 & Q6 & K1).
  assert (P2 : efa2_pre R1 (16 * sz - n - 4) (ef_slack sz n) (ef_off0 ctr h3 h16)).
  { constructor; [exact Q5 | exact Q6 | exact Q17 | clear - Fit Rt0; lia | reflexivity | apply land255_range]. }
  destruct (efa2_arm R1 m rom _ _ _ P2) as (R2 & M2 & S17 & K2).
  pose proof (ef_offv_rng sz n ctr h3 h16 Fit Rt0) as (OR & OS).
  assert (KEEP : forall k, In k [10;11;12;14;15;16]%nat -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr R1 (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. apply K2. clear - Hk. cbn [In efa2_keep] in *. tauto. }
  assert (P3 : efb_pre R2 m G idx n mem sz (ef_st mem sz idx) (ef_offv sz n ctr h3 h16)).
  { constructor.
    - etransitivity; [exact (KEEP 10%nat ltac:(clear; cbn; tauto)) | exact Q10].
    - etransitivity; [exact (KEEP 11%nat ltac:(clear; cbn; tauto)) | exact Q11].
    - etransitivity; [exact (KEEP 12%nat ltac:(clear; cbn; tauto)) | exact Q12].
    - etransitivity; [exact (KEEP 14%nat ltac:(clear; cbn; tauto)) | exact Q14].
    - etransitivity; [exact (KEEP 15%nat ltac:(clear; cbn; tauto)) | exact Q15].
    - etransitivity; [exact (KEEP 16%nat ltac:(clear; cbn; tauto)) | exact Q16].
    - exact S17.
    - exact RG.
    - exact AG.
    - exact Ridx.
    - clear - Rn; lia.
    - exact Rmem.
    - clear - Rsz; lia.
    - unfold ef_st. clear - RSLOT Rend Rsz. unfold ef_st in Rend. lia.
    - exact OR.
    - exact Mmem.
    - clear - OS Fit Rsz Rn. unfold ef_slack in OS. rewrite Z.shiftr_div_pow2 in OS by lia.
      assert (16 * ef_offv sz n ctr h3 h16 <= 16 * ((16 * sz - n - 4) / 2^4)) by lia.
      pose proof (Z.mul_div_le (16 * sz - n - 4) (2^4) ltac:(lia)). lia.
    - exact Rend.
    - unfold ef_st. clear - Ridx Rsz Ridx2. assert (0 <= sz * idx) by nia. lia.
    - unfold ef_st. replace (mem + 16 * sz * idx + 16 - mem) with ((sz * idx + 1) * 16) by ring. apply Z.mod_mul. lia.
    - exact Wok.
    - exact D. }
  destruct (efb_arm R2 m rom G idx n mem sz _ _ P3) as (R3 & M3 & T10 & K3).
  exists R3. split; [exact (msteps_trans SEGS _ _ _ M2 M3)|]. split; [exact T10|].
  intros k Hk. rewrite (K3 k Hk), (K2 k ltac:(clear - Hk; cbn [In callee_regs efa2_keep] in *; tauto)), (K1 k Hk). reflexivity.
Qed.

#[using="Type"] Theorem ef_class0_arm : forall regs m rom G idx n ctr W mem sz h3 h16, ef_pre regs m G idx n ctr W mem sz h3 h16 ->
  exists R, msteps SEGS (mkst regs (wa 0x5494c) m rom)
                        (mkst R (wa 0x54a98) (efb_mem m idx n mem sz (ef_st mem sz idx) (ef_offv sz n ctr h3 h16)) rom)
         /\ getr R 10 = wa (ef_st mem sz idx + 16 * ef_offv sz n ctr h3 h16)
         /\ (forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n ctr W mem sz h3 h16 P. destruct P as [A Rend Wok D].
  pose proof A as A'. destruct A' as [R10 R11 R12 R13 RG AG Ridx Rn Rctr RW Rmem Rsz Rh3 Rh16 RSLOT MW Mmem Msz M12 M13 M14 Fit].
  destruct (efa1_arm regs m rom G idx n ctr W mem sz h3 h16 A) as (R1 & M1 & P1).
  destruct (ef_after_a1 regs R1 m rom G idx n ctr mem sz h3 h16 P1 RG AG Ridx ltac:(lia) Rmem ltac:(lia) RSLOT Fit ltac:(lia)
              ltac:(clear - Ridx Rsz; assert (0 <= sz * idx <= 8191 * 31) by nia; lia) Mmem Rend Wok D) as (R & M & H10 & K).
  exists R. split; [exact (msteps_trans SEGS _ _ _ M1 M)|]. split; assumption.
Qed.

(* [comment removed for export] *)
Record efm_pre (regs : bvmap 5 word) (m : word -> option byte) (G idx n ctr W mem sz h3 h16 : Z) : Prop := {
  efm_A : efa1m_pre regs m G idx n ctr W mem sz h3 h16 ;
  efm_Rend : ef_st mem sz idx + 16 * sz <= 2^63 ;
  efm_W : forall d k, 0 <= d -> d + Z.of_nat k <= 16 * sz -> store_ok SEGS m (wa (ef_st mem sz idx - 4 + d)) k = true ;
  efm_D : G + 16 + 8 <= ef_st mem sz idx - 4 \/ ef_st mem sz idx - 4 + 16 * sz <= G + 16
}.

#[using="Type"] Theorem ef_classm_arm : forall regs m rom G idx n ctr W mem sz h3 h16, efm_pre regs m G idx n ctr W mem sz h3 h16 ->
  exists R, msteps SEGS (mkst regs (wa 0x5494c) m rom)
                        (mkst R (wa 0x54a98) (efb_mem m idx n mem sz (ef_st mem sz idx) (ef_offv sz n ctr h3 h16)) rom)
         /\ getr R 10 = wa (ef_st mem sz idx + 16 * ef_offv sz n ctr h3 h16)
         /\ (forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx n ctr W mem sz h3 h16 P. destruct P as [A Rend Wok D].
  pose proof A as A'. destruct A' as [R10 R11 R12 R13 RG AG Ridx Rn Rctr RW Wl Rmem Rsz Rh3 Rh16 RSLOT MW Mmem Msz M12 M13 M14 Fit].
  destruct (efa1m_arm regs m rom G idx n ctr W mem sz h3 h16 A) as (R1 & M1 & P1).
  destruct (ef_after_a1 regs R1 m rom G idx n ctr mem sz h3 h16 P1 RG AG Ridx ltac:(lia) Rmem ltac:(lia) RSLOT Fit ltac:(lia)
              ltac:(clear - Ridx Rsz; assert (0 <= sz * idx <= 8191 * 31) by nia; lia) Mmem Rend Wok D) as (R & M & H10 & K).
  exists R. split; [exact (msteps_trans SEGS _ _ _ M1 M)|]. split; assumption.
Qed.

(* [comment removed for export] *)
Record efd_pre (regs : bvmap 5 word) (m : word -> option byte) (G n ctr W mem h3 h16 : Z) : Prop := {
  efd_A : efa1d_pre regs m G n ctr W mem h3 h16 ;
  efd_t0 : ef_dstride W - n - 4 <= 131071 ;
  efd_W : forall d k, 0 <= d -> d + Z.of_nat k <= ef_dstride W -> store_ok SEGS m (wa (mem + 12 + d)) k = true ;
  efd_Rend : mem + 16 + ef_dstride W <= 2^63 ;
  efd_D : G + 16 + 8 <= mem + 12 \/ mem + 12 + ef_dstride W <= G + 16
}.

Definition ef_dsz (W : Z) : Z := 256 * Z.shiftr W 12 - 1.

#[using="Type"] Theorem ef_direct_arm : forall regs m rom G n ctr W mem h3 h16, efd_pre regs m G n ctr W mem h3 h16 ->
  exists R, msteps SEGS (mkst regs (wa 0x5494c) m rom)
                        (mkst R (wa 0x54a98) (efb_mem m 0 n mem (ef_dsz W) (ef_st mem (ef_dsz W) 0) (ef_offv (ef_dsz W) n ctr h3 h16)) rom)
         /\ getr R 10 = wa (ef_st mem (ef_dsz W) 0 + 16 * ef_offv (ef_dsz W) n ctr h3 h16)
         /\ (forall k, In k callee_regs -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G n ctr W mem h3 h16 P. destruct P as [A Rt0 Wok Rend D].
  pose proof A as A'. destruct A' as [R10 R11 R12 R13 RG AG Rn Rctr RW Wl Rmem Rh3 Rh16 MW Mmem M12 M13 M14 Fit Mend].
  pose proof (dstride_rng W RW) as (ML1 & ML2). unfold ef_dstride in *.
  destruct (efa1d_arm regs m rom G n ctr W mem h3 h16 A) as (R1 & M1 & P1).
  assert (E16 : 16 * ef_dsz W = 4096 * Z.shiftr W 12 - 16) by (unfold ef_dsz; ring).
  destruct (ef_after_a1 regs R1 m rom G 0 n ctr mem (ef_dsz W) h3 h16 P1 RG AG ltac:(lia) Rn Rmem) as (R & M & H10 & K).
  - unfold ef_dsz. clear - Fit Rn ML1 Rt0. lia.
  - lia.
  - rewrite E16. lia.
  - rewrite E16. lia.
  - lia.
  - exact Mmem.
  - unfold ef_st. rewrite E16. lia.
  - intros d k Hd Hk. unfold ef_st. replace (mem + 16 * ef_dsz W * 0 + 16 - 4 + d) with (mem + 12 + d) by ring. apply Wok; lia.
  - unfold ef_st. rewrite E16. replace (mem + 16 * ef_dsz W * 0 + 16 - 4) with (mem + 12) by ring. lia.
  - exists R. split; [exact (msteps_trans SEGS _ _ _ M1 M)|]. split; assumption.
Qed.

End EF.
