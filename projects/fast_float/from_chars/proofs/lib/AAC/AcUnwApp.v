(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put3.

Module AXF_uw0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_buf := EVar 32.
Definition e_pc := EVar 33.
Definition e_bp := EVar 34.
Definition e_top := EVar 35.
Definition e_bot := EVar 36.
Definition e_psz := EVar 37.
Definition STK := SA (EVar 2) (-1024).
Definition sr_uw0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_buf)) 11 (e_pc)) 12 (e_bp)) 13 (e_top)) 14 (e_bot)) 15 (ELit 30)).
Definition kn_uw0 : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWr STK (ELit 1024);
    KRange e_buf 1 (2^47);
    KAlign e_buf 8;
    KWr (SA e_buf 8) (ELit 248);
    KDisj STK (ELit 1024) (SA e_buf 8) (ELit 248);
    KWord (SA (ELit 0) 0xdcbf0) 8 (ELit 0x174860);
    KWord (SA (ELit 0) 0x174860) 8 e_psz;
    KImg 65536 143360;
    KDisj STK (ELit 1024) (SA (ELit 0) 0x174860) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0xdcbf0) (ELit 8) ].
Definition scr_uw0 : scripts := SCR [false; true; false; false; false; false] [] [].
Definition ss_uw0 := SS 0x82914 sr_uw0 [] kn_uw0 38.
Definition RUN_uw0 := sym_exec SEGS 60 true [0x829d4; 0x82a10] scr_uw0 ss_uw0 [].

Definition scr_puw0a : scripts := SCR [false; true; false; false; false; false] [] [].
Definition RES_puw0a := Eval vm_compute in sym_exec SEGS 60 true [0x829d4; 0x82a10] scr_puw0a ss_uw0 [].
Lemma RES_puw0a_ok : sym_exec SEGS 60 true [0x829d4; 0x82a10] scr_puw0a (SS 0x82914 sr_uw0 [] kn_uw0 38) [] = RES_puw0a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puw0b : scripts := SCR [false; true; false; true] [] [].
Definition RES_puw0b := Eval vm_compute in sym_exec SEGS 60 true [0x829d4; 0x82a10] scr_puw0b ss_uw0 [].
Lemma RES_puw0b_ok : sym_exec SEGS 60 true [0x829d4; 0x82a10] scr_puw0b (SS 0x82914 sr_uw0 [] kn_uw0 38) [] = RES_puw0b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puw0c : scripts := SCR [false; true; false; false; true] [] [].
Definition RES_puw0c := Eval vm_compute in sym_exec SEGS 60 true [0x829d4; 0x82a10] scr_puw0c ss_uw0 [].
Lemma RES_puw0c_ok : sym_exec SEGS 60 true [0x829d4; 0x82a10] scr_puw0c (SS 0x82914 sr_uw0 [] kn_uw0 38) [] = RES_puw0c.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puw0d : scripts := SCR [false; true; false; false; false; true] [] [].
Definition RES_puw0d := Eval vm_compute in sym_exec SEGS 60 true [0x829d4; 0x82a10] scr_puw0d ss_uw0 [].
Lemma RES_puw0d_ok : sym_exec SEGS 60 true [0x829d4; 0x82a10] scr_puw0d (SS 0x82914 sr_uw0 [] kn_uw0 38) [] = RES_puw0d.
Proof. vm_compute. reflexivity. Qed.
End AXF_uw0.

Module AXF_uw0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section UW0.
Context {fx : FPState}.

Definition VALS_uw0 (buf pc bp top bot psz : Z) : list Z := [buf; pc; bp; top; bot; psz].

Record uw0_pre (regs : bvmap 5 word) (m : word -> option byte) (buf pc bp top bot psz : Z) : Prop := {
  uw0_R10 : getr regs 10 = wa buf ;
  uw0_R11 : getr regs 11 = wa pc ;
  uw0_R12 : getr regs 12 = wa bp ;
  uw0_R13 : getr regs 13 = wa top ;
  uw0_R14 : getr regs 14 = wa bot ;
  uw0_R15 : getr regs 15 = wa 30 ;
  uw0_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  uw0_rng_buf : 1 <= buf <= 2^47 ;
  uw0_rng_pc : 0 <= pc <= 2^64-1 ;
  uw0_rng_bp : 0 <= bp <= 2^64-1 ;
  uw0_rng_top : 8192 <= top <= 2^47 ;
  uw0_rng_bot : 4096 <= bot <= 2^47 ;
  uw0_rng_psz : 4096 <= psz <= 4096 ;
  uw0_kr0 : (2^20) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  uw0_ka1 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) mod 16 = 0 ;
  uw0_ka4 : buf mod 8 = 0 ;
  uw0_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 248 -> store_ok SEGS m (wa (buf + 8 + d)) k = true ;
  uw0_kd6 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -1024 + 1024 <= buf + 8 \/ buf + 8 + 248 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -1024 ;
  uw0_kw7 : rdn SEGS m (wa (0 + 904176)) 8 = Some (word_to_le_bytes 8 (wa 1525856)) ;
  uw0_kw8 : rdn SEGS m (wa (0 + 1525856)) 8 = Some (word_to_le_bytes 8 (wa psz)) ;
  uw0_kimg9 : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None ;
  uw0_kd10 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -1024 + 1024 <= 0 + 1525856 \/ 0 + 1525856 + 8 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -1024 ;
  uw0_kd11 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -1024 + 1024 <= 0 + 904176 \/ 0 + 904176 + 8 <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -1024
}.


#[using="Type"] Lemma uw0_setup : forall regs m buf pc bp top bot psz, uw0_pre regs m buf pc bp top bot psz ->
  regs_ok (Ez regs (VALS_uw0 buf pc bp top bot psz)) AXF_uw0.sr_uw0 regs /\ know_ok SEGS (Ez regs (VALS_uw0 buf pc bp top bot psz)) m AXF_uw0.kn_uw0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m buf pc bp top bot psz P. destruct P as [uw0_R10 uw0_R11 uw0_R12 uw0_R13 uw0_R14 uw0_R15 uw0_HSTK uw0_rng_buf uw0_rng_pc uw0_rng_bp uw0_rng_top uw0_rng_bot uw0_rng_psz uw0_kr0 uw0_ka1 uw0_ka4 uw0_kwr5 uw0_kd6 uw0_kw7 uw0_kw8 uw0_kimg9 uw0_kd10 uw0_kd11].
  set (E := Ez regs (VALS_uw0 buf pc bp top bot psz)).
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = top) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = bot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = psz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  split.
  { unfold AXF_uw0.sr_uw0.
    apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite uw0_R10. reflexivity.
    - rewrite uw0_R11. reflexivity.
    - rewrite uw0_R12. reflexivity.
    - rewrite uw0_R13. reflexivity.
    - rewrite uw0_R14. reflexivity.
    - rewrite uw0_R15. reflexivity. }
  unfold know_ok, AXF_uw0.kn_uw0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_uw0.e_buf AXF_uw0.e_pc AXF_uw0.e_bp AXF_uw0.e_top AXF_uw0.e_bot AXF_uw0.e_psz AXF_uw0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range buf _ _ uw0_rng_buf eq_refl eq_refl), ?(mod64_of_range top _ _ uw0_rng_top eq_refl eq_refl), ?(mod64_of_range bot _ _ uw0_rng_bot eq_refl eq_refl), ?(mod64_of_range psz _ _ uw0_rng_psz eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply uw0_kwr5]; assumption).
  all: try (clear - uw0_rng_buf uw0_rng_pc uw0_rng_bp uw0_rng_top uw0_rng_bot uw0_rng_psz uw0_kr0 uw0_ka1 uw0_ka4; lia).
  all: first [(clear - uw0_rng_buf uw0_rng_pc uw0_rng_bp uw0_rng_top uw0_rng_bot uw0_rng_psz uw0_kr0 uw0_ka1 uw0_ka4 uw0_kd6; lia) | (clear - uw0_rng_buf uw0_rng_pc uw0_rng_bp uw0_rng_top uw0_rng_bot uw0_rng_psz uw0_kr0 uw0_ka1 uw0_ka4 uw0_kd10; lia) | (clear - uw0_rng_buf uw0_rng_pc uw0_rng_bp uw0_rng_top uw0_rng_bot uw0_rng_psz uw0_kr0 uw0_ka1 uw0_ka4 uw0_kd11; lia) | lia].
Qed.


Definition uw0_mem_puw0a (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp top bot psz : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (buf + 8)) (word_to_le_bytes 4 (wa 1))) (wa (buf + 16)) (word_to_le_bytes 8 (wa pc)).

#[using="Type"] Theorem uw0_puw0a : forall regs m rom buf pc bp top bot psz, uw0_pre regs m buf pc bp top bot psz ->
  scs_denot SEGS m (Ez regs (VALS_uw0 buf pc bp top bot psz)) (snd (fst AXF_uw0.RES_puw0a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x82914) m rom) (mkst R (wa 0x829d4) (uw0_mem_puw0a m regs buf pc bp top bot psz) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64) /\ getr R 8 = wa 30 /\ getr R 9 = wa (top + -16) /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa psz /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa 1 /\ getr R 16 = wa (Z.shiftr top 12) /\ getr R 18 = wa 1525856 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp top bot psz P Hsc. destruct (uw0_setup regs m buf pc bp top bot psz P) as [HR HK].
  set (E := Ez regs (VALS_uw0 buf pc bp top bot psz)) in *. destruct P as [uw0_R10 uw0_R11 uw0_R12 uw0_R13 uw0_R14 uw0_R15 uw0_HSTK uw0_rng_buf uw0_rng_pc uw0_rng_bp uw0_rng_top uw0_rng_bot uw0_rng_psz uw0_kr0 uw0_ka1 uw0_ka4 uw0_kwr5 uw0_kd6 uw0_kw7 uw0_kw8 uw0_kimg9 uw0_kd10 uw0_kd11].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = top) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = bot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = psz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  destruct (run_sound SEGS 60 [0x829d4; 0x82a10] AXF_uw0.scr_puw0a 0x82914 AXF_uw0.sr_uw0 AXF_uw0.kn_uw0 38 _ _ _ E m rom regs AXF_uw0.RES_puw0a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uw0.RES_puw0a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uw0_mem_puw0a m regs buf pc bp top bot psz) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uw0_mem_puw0a. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uw0_mem_puw0b (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp top bot psz : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (buf + 8)) (word_to_le_bytes 4 (wa 1))) (wa (buf + 16)) (word_to_le_bytes 8 (wa pc)).

#[using="Type"] Theorem uw0_puw0b : forall regs m rom buf pc bp top bot psz, uw0_pre regs m buf pc bp top bot psz ->
  scs_denot SEGS m (Ez regs (VALS_uw0 buf pc bp top bot psz)) (snd (fst AXF_uw0.RES_puw0b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x82914) m rom) (mkst R (wa 0x82a10) (uw0_mem_puw0b m regs buf pc bp top bot psz) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64) /\ getr R 8 = wa 30 /\ getr R 9 = wa top /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa psz /\ getr R 14 = wa bot /\ getr R 15 = wa 1 /\ getr R 16 = wa (Z.shiftr top 12) /\ getr R 18 = wa 1525856 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp top bot psz P Hsc. destruct (uw0_setup regs m buf pc bp top bot psz P) as [HR HK].
  set (E := Ez regs (VALS_uw0 buf pc bp top bot psz)) in *. destruct P as [uw0_R10 uw0_R11 uw0_R12 uw0_R13 uw0_R14 uw0_R15 uw0_HSTK uw0_rng_buf uw0_rng_pc uw0_rng_bp uw0_rng_top uw0_rng_bot uw0_rng_psz uw0_kr0 uw0_ka1 uw0_ka4 uw0_kwr5 uw0_kd6 uw0_kw7 uw0_kw8 uw0_kimg9 uw0_kd10 uw0_kd11].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = top) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = bot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = psz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  destruct (run_sound SEGS 60 [0x829d4; 0x82a10] AXF_uw0.scr_puw0b 0x82914 AXF_uw0.sr_uw0 AXF_uw0.kn_uw0 38 _ _ _ E m rom regs AXF_uw0.RES_puw0b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uw0.RES_puw0b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uw0_mem_puw0b m regs buf pc bp top bot psz) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uw0_mem_puw0b. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uw0_mem_puw0c (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp top bot psz : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (buf + 8)) (word_to_le_bytes 4 (wa 1))) (wa (buf + 16)) (word_to_le_bytes 8 (wa pc)).

#[using="Type"] Theorem uw0_puw0c : forall regs m rom buf pc bp top bot psz, uw0_pre regs m buf pc bp top bot psz ->
  scs_denot SEGS m (Ez regs (VALS_uw0 buf pc bp top bot psz)) (snd (fst AXF_uw0.RES_puw0c)) ->
  exists R, msteps SEGS (mkst regs (wa 0x82914) m rom) (mkst R (wa 0x82a10) (uw0_mem_puw0c m regs buf pc bp top bot psz) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64) /\ getr R 8 = wa 30 /\ getr R 9 = wa (top + -16) /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa psz /\ getr R 14 = wa bot /\ getr R 15 = wa 1 /\ getr R 16 = wa (Z.shiftr top 12) /\ getr R 18 = wa 1525856 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp top bot psz P Hsc. destruct (uw0_setup regs m buf pc bp top bot psz P) as [HR HK].
  set (E := Ez regs (VALS_uw0 buf pc bp top bot psz)) in *. destruct P as [uw0_R10 uw0_R11 uw0_R12 uw0_R13 uw0_R14 uw0_R15 uw0_HSTK uw0_rng_buf uw0_rng_pc uw0_rng_bp uw0_rng_top uw0_rng_bot uw0_rng_psz uw0_kr0 uw0_ka1 uw0_ka4 uw0_kwr5 uw0_kd6 uw0_kw7 uw0_kw8 uw0_kimg9 uw0_kd10 uw0_kd11].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = top) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = bot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = psz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  destruct (run_sound SEGS 60 [0x829d4; 0x82a10] AXF_uw0.scr_puw0c 0x82914 AXF_uw0.sr_uw0 AXF_uw0.kn_uw0 38 _ _ _ E m rom regs AXF_uw0.RES_puw0c_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uw0.RES_puw0c fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uw0_mem_puw0c m regs buf pc bp top bot psz) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uw0_mem_puw0c. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uw0_mem_puw0d (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp top bot psz : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (buf + 8)) (word_to_le_bytes 4 (wa 1))) (wa (buf + 16)) (word_to_le_bytes 8 (wa pc)).

#[using="Type"] Theorem uw0_puw0d : forall regs m rom buf pc bp top bot psz, uw0_pre regs m buf pc bp top bot psz ->
  scs_denot SEGS m (Ez regs (VALS_uw0 buf pc bp top bot psz)) (snd (fst AXF_uw0.RES_puw0d)) ->
  exists R, msteps SEGS (mkst regs (wa 0x82914) m rom) (mkst R (wa 0x82a10) (uw0_mem_puw0d m regs buf pc bp top bot psz) rom) /\
    getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64) /\ getr R 8 = wa 30 /\ getr R 9 = wa (top + -16) /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa psz /\ getr R 14 = wa (Z.land bp 7) /\ getr R 15 = wa 1 /\ getr R 16 = wa (Z.shiftr top 12) /\ getr R 18 = wa 1525856 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp top bot psz P Hsc. destruct (uw0_setup regs m buf pc bp top bot psz P) as [HR HK].
  set (E := Ez regs (VALS_uw0 buf pc bp top bot psz)) in *. destruct P as [uw0_R10 uw0_R11 uw0_R12 uw0_R13 uw0_R14 uw0_R15 uw0_HSTK uw0_rng_buf uw0_rng_pc uw0_rng_bp uw0_rng_top uw0_rng_bot uw0_rng_psz uw0_kr0 uw0_ka1 uw0_ka4 uw0_kwr5 uw0_kd6 uw0_kw7 uw0_kw8 uw0_kimg9 uw0_kd10 uw0_kd11].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = top) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = bot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = psz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  destruct (run_sound SEGS 60 [0x829d4; 0x82a10] AXF_uw0.scr_puw0d 0x82914 AXF_uw0.sr_uw0 AXF_uw0.kn_uw0 38 _ _ _ E m rom regs AXF_uw0.RES_puw0d_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uw0.RES_puw0d fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uw0_mem_puw0d m regs buf pc bp top bot psz) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uw0_mem_puw0d. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End UW0.
End AXF_uw0z.

Module AXF_uwl.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_buf := EVar 32.
Definition e_pc := EVar 33.
Definition e_bp := EVar 34.
Definition e_sz := EVar 35.
Definition e_s1v := EVar 36.
Definition e_w1 := EVar 37.
Definition e_nb := EVar 38.
Definition sr_uwl := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 30)) 9 (e_s1v)) 10 (e_buf)) 11 (e_pc)) 12 (e_bp)) 13 (ELit 4096)) 14 (EAlu ALU_ADD e_buf (ELit 16))) 15 (e_sz)).
Definition kn_uwl : list kentry :=
  [ KRange e_buf 1 (2^47);
    KAlign e_buf 8;
    KRange e_sz 1 30;
    KRange e_bp 16 (2^47);
    KAlign e_bp 8;
    KWr (SA e_buf 8) (ELit 4);
    KWr (SA (EAlu ALU_ADD e_buf (EMd M_MUL (ELit 8) e_sz)) 16) (ELit 8);
    KWord (SA e_bp (-8)) 8 e_w1;
    KWord (SA e_bp (-16)) 8 e_nb;
    KDisj (SA e_bp (-16)) (ELit 16) (SA e_buf 8) (ELit 248);
    KDisj (SA e_bp (-16)) (ELit 16) (SA (EAlu ALU_ADD e_buf (EMd M_MUL (ELit 8) e_sz)) 16) (ELit 8) ].
Definition scr_uwl : scripts := SCR [false; false; false; false; false; true] [] [].
Definition ss_uwl := SS 0x829d4 sr_uwl [] kn_uwl 39.
Definition RUN_uwl := sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_uwl ss_uwl [].

Definition scr_puwl1 : scripts := SCR [true] [] [].
Definition RES_puwl1 := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwl1 ss_uwl [].
Lemma RES_puwl1_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwl1 (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwl1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puwl2 : scripts := SCR [false; true] [] [].
Definition RES_puwl2 := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwl2 ss_uwl [].
Lemma RES_puwl2_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwl2 (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwl2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puwlk3 : scripts := SCR [false; false; true; true] [] [].
Definition RES_puwlk3 := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlk3 ss_uwl [].
Lemma RES_puwlk3_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlk3 (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwlk3.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puwlk4 : scripts := SCR [false; false; true; false; true] [] [].
Definition RES_puwlk4 := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlk4 ss_uwl [].
Lemma RES_puwlk4_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlk4 (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwlk4.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puwlk5 : scripts := SCR [false; false; true; false; false; false] [] [].
Definition RES_puwlk5 := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlk5 ss_uwl [].
Lemma RES_puwlk5_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlk5 (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwlk5.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puwlkc : scripts := SCR [false; false; true; false; false; true] [] [].
Definition RES_puwlkc := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlkc ss_uwl [].
Lemma RES_puwlkc_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlkc (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwlkc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puwls3 : scripts := SCR [false; false; false; true] [] [].
Definition RES_puwls3 := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwls3 ss_uwl [].
Lemma RES_puwls3_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwls3 (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwls3.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puwls4 : scripts := SCR [false; false; false; false; true] [] [].
Definition RES_puwls4 := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwls4 ss_uwl [].
Lemma RES_puwls4_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwls4 (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwls4.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puwls5 : scripts := SCR [false; false; false; false; false; false] [] [].
Definition RES_puwls5 := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwls5 ss_uwl [].
Lemma RES_puwls5_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwls5 (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwls5.
Proof. vm_compute. reflexivity. Qed.

Definition scr_puwlsc : scripts := SCR [false; false; false; false; false; true] [] [].
Definition RES_puwlsc := Eval vm_compute in sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlsc ss_uwl [].
Lemma RES_puwlsc_ok : sym_exec SEGS 30 true [0x829d4; 0x82a10] scr_puwlsc (SS 0x829d4 sr_uwl [] kn_uwl 39) [] = RES_puwlsc.
Proof. vm_compute. reflexivity. Qed.
End AXF_uwl.

Module AXF_uwlz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section UWL.
Context {fx : FPState}.

Definition VALS_uwl (buf pc bp sz s1v w1 nb : Z) : list Z := [buf; pc; bp; sz; s1v; w1; nb].

Record uwl_pre (regs : bvmap 5 word) (m : word -> option byte) (buf pc bp sz s1v w1 nb : Z) : Prop := {
  uwl_R8 : getr regs 8 = wa 30 ;
  uwl_R9 : getr regs 9 = wa s1v ;
  uwl_R10 : getr regs 10 = wa buf ;
  uwl_R11 : getr regs 11 = wa pc ;
  uwl_R12 : getr regs 12 = wa bp ;
  uwl_R13 : getr regs 13 = wa 4096 ;
  uwl_R14 : getr regs 14 = wa (buf + 16) ;
  uwl_R15 : getr regs 15 = wa sz ;
  uwl_rng_buf : 1 <= buf <= 2^47 ;
  uwl_rng_pc : 0 <= pc <= 2^64-1 ;
  uwl_rng_bp : 16 <= bp <= 2^47 ;
  uwl_rng_sz : 1 <= sz <= 30 ;
  uwl_rng_s1v : 0 <= s1v <= 2^47 ;
  uwl_rng_w1 : 0 <= w1 <= 2^64-1 ;
  uwl_rng_nb : 0 <= nb <= 2^64-1 ;
  uwl_ka1 : buf mod 8 = 0 ;
  uwl_ka4 : bp mod 8 = 0 ;
  uwl_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (buf + 8 + d)) k = true ;
  uwl_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (buf + (8 * sz) + 16 + d)) k = true ;
  uwl_kw7 : rdn SEGS m (wa (bp + -8)) 8 = Some (word_to_le_bytes 8 (wa w1)) ;
  uwl_kw8 : rdn SEGS m (wa (bp + -16)) 8 = Some (word_to_le_bytes 8 (wa nb)) ;
  uwl_kd9 : bp + -16 + 16 <= buf + 8 \/ buf + 8 + 248 <= bp + -16 ;
  uwl_kd10 : bp + -16 + 16 <= buf + (8 * sz) + 16 \/ buf + (8 * sz) + 16 + 8 <= bp + -16
}.


#[using="Type"] Lemma uwl_setup : forall regs m buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  regs_ok (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) AXF_uwl.sr_uwl regs /\ know_ok SEGS (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) m AXF_uwl.kn_uwl.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m buf pc bp sz s1v w1 nb P. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)).
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_uwl.sr_uwl.
    apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|]|]|].
    - rewrite uwl_R8. reflexivity.
    - rewrite uwl_R9. reflexivity.
    - rewrite uwl_R10. reflexivity.
    - rewrite uwl_R11. reflexivity.
    - rewrite uwl_R12. reflexivity.
    - rewrite uwl_R13. reflexivity.
    - rewrite uwl_R14, zeval_sound. cbn [zeval edenot AXF_uwl.e_buf AXF_uwl.e_pc AXF_uwl.e_bp AXF_uwl.e_sz AXF_uwl.e_s1v AXF_uwl.e_w1 AXF_uwl.e_nb]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite uwl_R15. reflexivity. }
  unfold know_ok, AXF_uwl.kn_uwl.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_uwl.e_buf AXF_uwl.e_pc AXF_uwl.e_bp AXF_uwl.e_sz AXF_uwl.e_s1v AXF_uwl.e_w1 AXF_uwl.e_nb a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range buf _ _ uwl_rng_buf eq_refl eq_refl), ?(mod64_of_range bp _ _ uwl_rng_bp eq_refl eq_refl), ?(mod64_of_range sz _ _ uwl_rng_sz eq_refl eq_refl), ?(mod64_of_range s1v _ _ uwl_rng_s1v eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply uwl_kwr5 | apply uwl_kwr6]; assumption).
  all: try (clear - uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4; lia).
  all: first [(clear - uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kd9; lia) | (clear - uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kd10; lia) | lia].
Qed.


Definition uwl_mem_puwl1 (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem uwl_puwl1 : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwl1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x82a10) (uwl_mem_puwl1 m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa sz /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwl1 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwl1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwl1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwl1 m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwl1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uwl_mem_puwl2 (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem uwl_puwl2 : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwl2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x82a10) (uwl_mem_puwl2 m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa sz /\ getr R 16 = wa w1 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwl2 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwl2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwl2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwl2 m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwl2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uwl_mem_puwlk3 (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem uwl_puwlk3 : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwlk3)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x82a10) (uwl_mem_puwlk3 m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa sz /\ getr R 16 = wa nb /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwlk3 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwlk3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwlk3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwlk3 m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwlk3. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uwl_mem_puwlk4 (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem uwl_puwlk4 : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwlk4)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x82a10) (uwl_mem_puwlk4 m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa sz /\ getr R 16 = wa nb /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwlk4 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwlk4_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwlk4 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwlk4 m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwlk4. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uwl_mem_puwlk5 (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem uwl_puwlk5 : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwlk5)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x82a10) (uwl_mem_puwlk5 m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa nb /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa sz /\ getr R 16 = wa nb /\ getr R 17 = wa (Z.land nb 7) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwlk5 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwlk5_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwlk5 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwlk5 m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwlk5. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uwl_mem_puwlkc (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem uwl_puwlkc : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwlkc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x829d4) (uwl_mem_puwlkc m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa nb /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa sz /\ getr R 16 = wa nb /\ getr R 17 = wa (Z.land nb 7) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwlkc 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwlkc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwlkc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwlkc m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwlkc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uwl_mem_puwls3 (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (buf + 8)) (word_to_le_bytes 4 (wa (sz + 1)))) (wa (buf + (8 * sz) + 16)) (word_to_le_bytes 8 (wa w1)).

#[using="Type"] Theorem uwl_puwls3 : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwls3)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x82a10) (uwl_mem_puwls3 m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa (sz + 1) /\ getr R 16 = wa nb /\ getr R 17 = wa ((buf + (8 * sz)) + 16) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwls3 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwls3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwls3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwls3 m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwls3. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uwl_mem_puwls4 (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (buf + 8)) (word_to_le_bytes 4 (wa (sz + 1)))) (wa (buf + (8 * sz) + 16)) (word_to_le_bytes 8 (wa w1)).

#[using="Type"] Theorem uwl_puwls4 : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwls4)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x82a10) (uwl_mem_puwls4 m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa (sz + 1) /\ getr R 16 = wa nb /\ getr R 17 = wa ((buf + (8 * sz)) + 16) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwls4 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwls4_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwls4 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwls4 m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwls4. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uwl_mem_puwls5 (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (buf + 8)) (word_to_le_bytes 4 (wa (sz + 1)))) (wa (buf + (8 * sz) + 16)) (word_to_le_bytes 8 (wa w1)).

#[using="Type"] Theorem uwl_puwls5 : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwls5)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x82a10) (uwl_mem_puwls5 m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa nb /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa (sz + 1) /\ getr R 16 = wa nb /\ getr R 17 = wa (Z.land nb 7) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwls5 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwls5_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwls5 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwls5 m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwls5. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition uwl_mem_puwlsc (m : word -> option byte) (regs : bvmap 5 word) (buf pc bp sz s1v w1 nb : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (buf + 8)) (word_to_le_bytes 4 (wa (sz + 1)))) (wa (buf + (8 * sz) + 16)) (word_to_le_bytes 8 (wa w1)).

#[using="Type"] Theorem uwl_puwlsc : forall regs m rom buf pc bp sz s1v w1 nb, uwl_pre regs m buf pc bp sz s1v w1 nb ->
  scs_denot SEGS m (Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) (snd (fst AXF_uwl.RES_puwlsc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x829d4) m rom) (mkst R (wa 0x829d4) (uwl_mem_puwlsc m regs buf pc bp sz s1v w1 nb) rom) /\
    getr R 8 = wa 30 /\ getr R 9 = wa s1v /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa nb /\ getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa (sz + 1) /\ getr R 16 = wa nb /\ getr R 17 = wa (Z.land nb 7) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom buf pc bp sz s1v w1 nb P Hsc. destruct (uwl_setup regs m buf pc bp sz s1v w1 nb P) as [HR HK].
  set (E := Ez regs (VALS_uwl buf pc bp sz s1v w1 nb)) in *. destruct P as [uwl_R8 uwl_R9 uwl_R10 uwl_R11 uwl_R12 uwl_R13 uwl_R14 uwl_R15 uwl_rng_buf uwl_rng_pc uwl_rng_bp uwl_rng_sz uwl_rng_s1v uwl_rng_w1 uwl_rng_nb uwl_ka1 uwl_ka4 uwl_kwr5 uwl_kwr6 uwl_kw7 uwl_kw8 uwl_kd9 uwl_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = buf) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = pc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = bp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s1v) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = w1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 30 [0x829d4; 0x82a10] AXF_uwl.scr_puwlsc 0x829d4 AXF_uwl.sr_uwl AXF_uwl.kn_uwl 39 _ _ _ E m rom regs AXF_uwl.RES_puwlsc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwl.RES_puwlsc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwl_mem_puwlsc m regs buf pc bp sz s1v w1 nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwl_mem_puwlsc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End UWL.
End AXF_uwlz.

Module AXF_uwe.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_rp := EVar 40.
Definition e_v0 := EVar 41.
Definition e_v1 := EVar 42.
Definition e_v2 := EVar 43.
Definition e_v3 := EVar 44.
Definition e_v4 := EVar 45.
Definition e_v5 := EVar 46.
Definition e_v6 := EVar 47.
Definition sr_uwe := sr_id.
Definition kn_uwe : list kentry :=
  [ KRange (EVar 2) (2^20) (2^47);
    KAlign (EVar 2) 16;
    KWord (SA (EVar 2) 56) 8 e_rp;
    KWord (SA (EVar 2) 48) 8 e_v0;
    KWord (SA (EVar 2) 40) 8 e_v1;
    KWord (SA (EVar 2) 32) 8 e_v2;
    KWord (SA (EVar 2) 24) 8 e_v3;
    KWord (SA (EVar 2) 16) 8 e_v4;
    KWord (SA (EVar 2) 8) 8 e_v5;
    KWord (SA (EVar 2) 0) 8 e_v6 ].
Definition scr_uwe : scripts := SCR [] [] [].
Definition ss_uwe := SS 0x82a10 sr_uwe [] kn_uwe 48.
Definition RUN_uwe := sym_exec SEGS 20 true [0x82a34] scr_uwe ss_uwe [].

Definition scr_puwe : scripts := SCR [] [] [].
Definition RES_puwe := Eval vm_compute in sym_exec SEGS 20 true [0x82a34] scr_puwe ss_uwe [].
Lemma RES_puwe_ok : sym_exec SEGS 20 true [0x82a34] scr_puwe (SS 0x82a10 sr_uwe [] kn_uwe 48) [] = RES_puwe.
Proof. vm_compute. reflexivity. Qed.
End AXF_uwe.

Module AXF_uwez.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section UWE.
Context {fx : FPState}.

Definition VALS_uwe (rp v0 v1 v2 v3 v4 v5 v6 : Z) : list Z := [0; 0; 0; 0; 0; 0; 0; 0; rp; v0; v1; v2; v3; v4; v5; v6].

Record uwe_pre (regs : bvmap 5 word) (m : word -> option byte) (rp v0 v1 v2 v3 v4 v5 v6 : Z) : Prop := {
  uwe_rng_rp : 0 <= rp <= 2^64-1 ;
  uwe_rng_v0 : 0 <= v0 <= 2^64-1 ;
  uwe_rng_v1 : 0 <= v1 <= 2^64-1 ;
  uwe_rng_v2 : 0 <= v2 <= 2^64-1 ;
  uwe_rng_v3 : 0 <= v3 <= 2^64-1 ;
  uwe_rng_v4 : 0 <= v4 <= 2^64-1 ;
  uwe_rng_v5 : 0 <= v5 <= 2^64-1 ;
  uwe_rng_v6 : 0 <= v6 <= 2^64-1 ;
  uwe_kr0 : (2^20) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  uwe_ka1 : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) mod 16 = 0 ;
  uwe_kw2 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 56)) 8 = Some (word_to_le_bytes 8 (wa rp)) ;
  uwe_kw3 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 48)) 8 = Some (word_to_le_bytes 8 (wa v0)) ;
  uwe_kw4 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 40)) 8 = Some (word_to_le_bytes 8 (wa v1)) ;
  uwe_kw5 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 32)) 8 = Some (word_to_le_bytes 8 (wa v2)) ;
  uwe_kw6 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 24)) 8 = Some (word_to_le_bytes 8 (wa v3)) ;
  uwe_kw7 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 16)) 8 = Some (word_to_le_bytes 8 (wa v4)) ;
  uwe_kw8 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 8)) 8 = Some (word_to_le_bytes 8 (wa v5)) ;
  uwe_kw9 : rdn SEGS m (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 0)) 8 = Some (word_to_le_bytes 8 (wa v6))
}.


#[using="Type"] Lemma uwe_setup : forall regs m rp v0 v1 v2 v3 v4 v5 v6, uwe_pre regs m rp v0 v1 v2 v3 v4 v5 v6 ->
  regs_ok (Ez regs (VALS_uwe rp v0 v1 v2 v3 v4 v5 v6)) AXF_uwe.sr_uwe regs /\ know_ok SEGS (Ez regs (VALS_uwe rp v0 v1 v2 v3 v4 v5 v6)) m AXF_uwe.kn_uwe.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rp v0 v1 v2 v3 v4 v5 v6 P. destruct P as [uwe_rng_rp uwe_rng_v0 uwe_rng_v1 uwe_rng_v2 uwe_rng_v3 uwe_rng_v4 uwe_rng_v5 uwe_rng_v6 uwe_kr0 uwe_ka1 uwe_kw2 uwe_kw3 uwe_kw4 uwe_kw5 uwe_kw6 uwe_kw7 uwe_kw8 uwe_kw9].
  set (E := Ez regs (VALS_uwe rp v0 v1 v2 v3 v4 v5 v6)).
  assert (Z40 : bv_unsigned (ev E 40) = rp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = v0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = v1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = v2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = v3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = v4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = v5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = v6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  split.
  { unfold AXF_uwe.sr_uwe.
    apply regs_ok_id.
 }
  unfold know_ok, AXF_uwe.kn_uwe.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_uwe.e_rp AXF_uwe.e_v0 AXF_uwe.e_v1 AXF_uwe.e_v2 AXF_uwe.e_v3 AXF_uwe.e_v4 AXF_uwe.e_v5 AXF_uwe.e_v6 a_base a_off].
  all: rewrite ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45, ?Z46, ?Z47, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - uwe_rng_rp uwe_rng_v0 uwe_rng_v1 uwe_rng_v2 uwe_rng_v3 uwe_rng_v4 uwe_rng_v5 uwe_rng_v6 uwe_kr0 uwe_ka1; lia).
  all: first [lia].
Qed.


Definition uwe_mem_puwe (m : word -> option byte) (regs : bvmap 5 word) (rp v0 v1 v2 v3 v4 v5 v6 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem uwe_puwe : forall regs m rom rp v0 v1 v2 v3 v4 v5 v6, uwe_pre regs m rp v0 v1 v2 v3 v4 v5 v6 ->
  scs_denot SEGS m (Ez regs (VALS_uwe rp v0 v1 v2 v3 v4 v5 v6)) (snd (fst AXF_uwe.RES_puwe)) ->
  exists R, msteps SEGS (mkst regs (wa 0x82a10) m rom) (mkst R (wa 0x82a34) (uwe_mem_puwe m regs rp v0 v1 v2 v3 v4 v5 v6) rom) /\
    getr R 1 = wa rp /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + 64) /\ getr R 8 = wa v0 /\ getr R 9 = wa v1 /\ getr R 18 = wa v2 /\ getr R 19 = wa v3 /\ getr R 20 = wa v4 /\ getr R 21 = wa v5 /\ getr R 22 = wa v6 /\ (forall k, In k [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom rp v0 v1 v2 v3 v4 v5 v6 P Hsc. destruct (uwe_setup regs m rp v0 v1 v2 v3 v4 v5 v6 P) as [HR HK].
  set (E := Ez regs (VALS_uwe rp v0 v1 v2 v3 v4 v5 v6)) in *. destruct P as [uwe_rng_rp uwe_rng_v0 uwe_rng_v1 uwe_rng_v2 uwe_rng_v3 uwe_rng_v4 uwe_rng_v5 uwe_rng_v6 uwe_kr0 uwe_ka1 uwe_kw2 uwe_kw3 uwe_kw4 uwe_kw5 uwe_kw6 uwe_kw7 uwe_kw8 uwe_kw9].
  assert (Z40 : bv_unsigned (ev E 40) = rp) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = v0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = v1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = v2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = v3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = v4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z46 : bv_unsigned (ev E 46) = v5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z47 : bv_unsigned (ev E 47) = v6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.
  destruct (run_sound SEGS 20 [0x82a34] AXF_uwe.scr_puwe 0x82a10 AXF_uwe.sr_uwe AXF_uwe.kn_uwe 48 _ _ _ E m rom regs AXF_uwe.RES_puwe_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_uwe.RES_puwe fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (uwe_mem_puwe m regs rp v0 v1 v2 v3 v4 v5 v6) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold uwe_mem_puwe. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End UWE.
End AXF_uwez.

Module AXG_uw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan AXG_put AXG_put2.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac is_arith T := lazymatch T with
  | @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac | Nat.le _ _ => idtac | Nat.lt _ _ => idtac | le _ _ => idtac | lt _ _ => idtac
  | ?A /\ ?B => is_arith A; is_arith B
  | ?A \/ ?B => is_arith A; is_arith B
  | ~ ?A => is_arith A
  | True => idtac | False => idtac
  end.
Ltac prune_ctx := repeat match goal with
  | H : ?T |- _ => lazymatch type of T with
                   | Prop => tryif is_arith T then fail else clear H
                   | _ => fail
                   end
  end.
Ltac prune_mod := lazymatch goal with
  | |- context [Z.modulo _ _] => idtac
  | |- context [Z.div _ _] => idtac
  | _ => repeat match goal with
              | H : Z.modulo _ _ = _ |- _ => clear H
              | H : context [Z.modulo _ _] |- _ => lazymatch type of H with _ /\ _ => let H1 := fresh "C" in let H2 := fresh "C" in pose proof H as [H1 H2]; clear H end
              end
  end.
Ltac slia := first [ LiaFast.lia_fast_tiers | (prune_ctx; prune_mod; lia) ].
Ltac srdwb := repeat first [ (apply wb_rd_hit; first [slia | (lenb; slia)]) | (apply wb_rd_other; [slia | slia | slia | lenb; slia | lenb; slia | ]) ].
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Ltac scgo := repeat (first [apply Forall_nil | apply Forall_cons]).
Ltac rgz := replace (Z_to_bv 5 (Z.of_nat 2)) with (@BV 5 2 I) in * by (apply bv_eq; reflexivity).

Lemma rd_some : forall m a bs, rdn SEGS m (wa a) 8 = Some bs -> exists v, 0 <= v < 2^64 /\ rdn SEGS m (wa a) 8 = Some (word_to_le_bytes 8 (wa v)).
Proof.
  intros m a bs H. destruct (rd_exists m a 8 bs ltac:(slia) H) as (v & Hv1 & Hv2 & Hrd). exists v. split; [slia|].
  unfold rd in Hrd. rewrite Hrd. reflexivity.
Qed.

Lemma u_rng : forall w : word, 0 <= bv_unsigned w <= 2^64 - 1.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2^64) in H. slia. Qed.

Ltac zat := repeat match goal with |- context [bv_unsigned (ev (Ez ?R ?V) ?n)] =>
              let v := eval cbn [nth Nat.sub AXF_uwlz.VALS_uwl AXF_uw0z.VALS_uw0 AXF_uwez.VALS_uwe] in (nth (n - 32) V 0) in
              rewrite (zatom R V n v eq_refl eq_refl) by slia end.
Ltac bfin := first [ reflexivity | (apply negb_true_iff; first [apply Z.ltb_ge | apply Z.eqb_neq]; slia)
                   | (apply negb_false_iff; first [apply Z.ltb_lt | apply Z.eqb_eq]; slia)
                   | (apply Z.ltb_lt; slia) | (apply Z.ltb_ge; slia) | (apply Z.eqb_eq; slia) | (apply Z.eqb_neq; slia) ].
Ltac uwsc1 := apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z];
             cbn [zeval edenot]; zat; rewrite ?(Z.mod_small _ (2^64)) by slia.
Ltac uwsc := scgo; uwsc1; try bfin.
Ltac lastK H := repeat (destruct H as [_ H]).
Ltac andfin b Hal := rewrite (Z.mod_small b (2^64)) by slia; change (7 mod 2^64) with 7; rewrite Hal;
                     rewrite (Z.mod_small (b mod 8) (2^64)) by slia; change (0 mod 2^64) with 0; bfin.



(* [comment removed for export] *)
Section SC.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (buf pc bp sz s1v w1 nb : Z).
Hypothesis Hr : 0 <= pc < 2^64 /\ 0 <= bp < 2^64 /\ 1 <= sz <= 30 /\ 0 <= w1 < 2^64 /\ 0 <= nb < 2^64.
Let E := Ez R (AXF_uwlz.VALS_uwl buf pc bp sz s1v w1 nb).
#[using="Hr"] Lemma sc_l1 : 30 <= sz -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwl1)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_uwl.RES_puwl1 fst snd]. unfold E. uwsc. Qed.
#[using="Hr"] Lemma sc_l2 : sz < 30 -> w1 < 4096 -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwl2)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H1 H2. cbn [AXF_uwl.RES_puwl2 fst snd]. unfold E. uwsc. Qed.
#[using="Hr"] Lemma sc_k3 : sz < 30 -> 4096 <= w1 -> w1 = pc -> nb <= bp -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwlk3)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H1 H2 H3 H4. cbn [AXF_uwl.RES_puwlk3 fst snd]. unfold E. uwsc. Qed.
#[using="Hr"] Lemma sc_k4 : sz < 30 -> 4096 <= w1 -> w1 = pc -> bp < nb -> s1v <= nb -> 0 <= s1v < 2^64 -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwlk4)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H1 H2 H3 H4 H5 H6. cbn [AXF_uwl.RES_puwlk4 fst snd]. unfold E. uwsc. Qed.
#[using="Hr"] Lemma sc_s3 : sz < 30 -> 4096 <= w1 -> w1 <> pc -> nb <= bp -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwls3)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H1 H2 H3 H4. cbn [AXF_uwl.RES_puwls3 fst snd]. unfold E. uwsc. Qed.
#[using="Hr"] Lemma sc_s4 : sz < 30 -> 4096 <= w1 -> w1 <> pc -> bp < nb -> s1v <= nb -> 0 <= s1v < 2^64 -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwls4)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H1 H2 H3 H4 H5 H6. cbn [AXF_uwl.RES_puwls4 fst snd]. unfold E. uwsc. Qed.
#[using="Type"] Lemma land7 : forall z, 0 <= z < 2^64 -> Z.land z 7 = z mod 8.
Proof. LiaFast.lf_pins LiaFast.u0. intros z Hz. change 7 with (Z.ones 3). rewrite Z.land_ones by slia. reflexivity. Qed.
#[using="Hr"] Lemma sc_k5 : sz < 30 -> 4096 <= w1 -> w1 = pc -> bp < nb -> nb < s1v -> 0 <= s1v < 2^64 -> nb mod 8 <> 0 -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwlk5)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H1 H2 H3 H4 H5 H6 H7. pose proof (Z.mod_pos_bound nb 8 ltac:(slia)). pose proof (land7 nb ltac:(slia)). cbn [AXF_uwl.RES_puwlk5 fst snd]. unfold E. scgo; uwsc1; try bfin; andfin nb H0. Qed.
#[using="Hr"] Lemma sc_kc : sz < 30 -> 4096 <= w1 -> w1 = pc -> bp < nb -> nb < s1v -> 0 <= s1v < 2^64 -> nb mod 8 = 0 -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwlkc)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H1 H2 H3 H4 H5 H6 H7. pose proof (Z.mod_pos_bound nb 8 ltac:(slia)). pose proof (land7 nb ltac:(slia)). cbn [AXF_uwl.RES_puwlkc fst snd]. unfold E. scgo; uwsc1; try bfin; andfin nb H0. Qed.
#[using="Hr"] Lemma sc_s5 : sz < 30 -> 4096 <= w1 -> w1 <> pc -> bp < nb -> nb < s1v -> 0 <= s1v < 2^64 -> nb mod 8 <> 0 -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwls5)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H1 H2 H3 H4 H5 H6 H7. pose proof (Z.mod_pos_bound nb 8 ltac:(slia)). pose proof (land7 nb ltac:(slia)). cbn [AXF_uwl.RES_puwls5 fst snd]. unfold E. scgo; uwsc1; try bfin; andfin nb H0. Qed.
#[using="Hr"] Lemma sc_sc : sz < 30 -> 4096 <= w1 -> w1 <> pc -> bp < nb -> nb < s1v -> 0 <= s1v < 2^64 -> nb mod 8 = 0 -> scs_denot SEGS m E (snd (fst AXF_uwl.RES_puwlsc)).
Proof. LiaFast.lf_pins (fun (Hr : LiaFast.U) => LiaFast.u0). intros H1 H2 H3 H4 H5 H6 H7. pose proof (Z.mod_pos_bound nb 8 ltac:(slia)). pose proof (land7 nb ltac:(slia)). cbn [AXF_uwl.RES_puwlsc fst snd]. unfold E. scgo; uwsc1; try bfin; andfin nb H0. Qed.
End SC.

(* [comment removed for export] *)
Section SC0.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (buf pc bp top bot : Z).
Hypothesis Hr : 0 <= pc < 2^64 /\ 0 <= bp < 2^64 /\ 8192 <= top <= 2^47 /\ 4096 <= bot < top /\ 1 <= buf <= 2^47.
Hypothesis Hshg : negb ((top mod 2^64) ≫ (12 mod 64) mod 2^64 =? 0 mod 2^64) = true.
Let E := Ez R (AXF_uw0z.VALS_uw0 buf pc bp top bot 4096).
#[using="Hr Hshg"] Lemma sc0b : bp <= bot -> scs_denot SEGS m E (snd (fst AXF_uw0.RES_puw0b)).
Proof. LiaFast.lf_pins (fun (Hr Hshg : LiaFast.U) => LiaFast.u0). intros H1. cbn [AXF_uw0.RES_puw0b fst snd]. unfold E. uwsc. all: try exact Hshg. Qed.
#[using="Hr Hshg"] Lemma sc0c : bot < bp -> top - 16 <= bp -> scs_denot SEGS m E (snd (fst AXF_uw0.RES_puw0c)).
Proof. LiaFast.lf_pins (fun (Hr Hshg : LiaFast.U) => LiaFast.u0). intros H1 H2. cbn [AXF_uw0.RES_puw0c fst snd]. unfold E. uwsc. all: try exact Hshg. Qed.
#[using="Hr Hshg"] Lemma sc0d : bot < bp -> bp < top - 16 -> bp mod 8 <> 0 -> scs_denot SEGS m E (snd (fst AXF_uw0.RES_puw0d)).
Proof. LiaFast.lf_pins (fun (Hr Hshg : LiaFast.U) => LiaFast.u0).
  intros H1 H2 H3. assert (Hal : Z.land bp 7 = bp mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by slia; reflexivity).
  pose proof (Z.mod_pos_bound bp 8 ltac:(slia)). cbn [AXF_uw0.RES_puw0d fst snd]. unfold E. scgo; uwsc1; try exact Hshg; try bfin; andfin bp Hal.
Qed.
#[using="Hr Hshg"] Lemma sc0a : bot < bp -> bp < top - 16 -> bp mod 8 = 0 -> scs_denot SEGS m E (snd (fst AXF_uw0.RES_puw0a)).
Proof. LiaFast.lf_pins (fun (Hr Hshg : LiaFast.U) => LiaFast.u0).
  intros H1 H2 H3. assert (Hal : Z.land bp 7 = bp mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by slia; reflexivity).
  pose proof (Z.mod_pos_bound bp 8 ltac:(slia)). cbn [AXF_uw0.RES_puw0a fst snd]. unfold E. scgo; uwsc1; try exact Hshg; try bfin; andfin bp Hal.
Qed.
End SC0.

Section UW.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m0 : word -> option byte) (regs0 : bvmap 5 word) (SP buf pc bp0 top bot : Z).
Hypothesis HR2 : getr regs0 2 = wa SP.
Hypothesis HR10 : getr regs0 10 = wa buf.
Hypothesis HR11 : getr regs0 11 = wa pc.
Hypothesis HR12 : getr regs0 12 = wa bp0.
Hypothesis HR13 : getr regs0 13 = wa top.
Hypothesis HR14 : getr regs0 14 = wa bot.
Hypothesis HR15 : getr regs0 15 = wa 30.
Hypothesis HSP : 2^22 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m0 (wa SP) 1024.
Hypothesis Hbuf : SP <= buf /\ buf + 2056 <= 2^47 /\ buf mod 8 = 0.
Hypothesis HWB : forall d k, 0 <= d -> d + Z.of_nat k <= 2048 -> store_ok SEGS m0 (wa (buf + 8 + d)) k = true.
Hypothesis HGOT : rdn SEGS m0 (wa 904176) 8 = Some (word_to_le_bytes 8 (wa 1525856)).
Hypothesis HPSZ : rdn SEGS m0 (wa 1525856) 8 = Some (word_to_le_bytes 8 (wa 4096)).
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m0 (Z_to_bv 64 i) = None.
Hypothesis Htb : 8192 <= top <= 2^47 /\ 4096 <= bot < top.
Hypothesis Hpc : 0 <= pc < 2^64.
Hypothesis Hbp0 : 0 <= bp0 < 2^64.
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive uch : Z -> Prop :=
| uch_mk : forall bp, (exists bs, rdn SEGS m0 (wa (bp - 8)) 8 = Some bs) -> (exists bs, rdn SEGS m0 (wa (bp - 16)) 8 = Some bs) ->
    (forall nb, rd m0 (bp - 16) 8 nb -> bp < nb -> nb < top - 16 -> nb mod 8 = 0 -> uch nb) -> uch bp.
Hypothesis HCH : bot < bp0 -> uch bp0.
Hypothesis Hbp0b : bot < bp0 -> buf + 256 + 32 <= bp0.

Definition KSAVE : list nat := [1; 8; 9; 18; 19; 20; 21; 22]%nat.
Definition KALL : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

(* [comment removed for export] *)
Definition WUW (x : Z) : Prop := (SP - 64 <= x < SP) \/ (buf + 8 <= x < buf + 12) \/ (buf + 16 <= x < buf + 256).

Section LOOP.
Variables (R1 : bvmap 5 word) (m1 : word -> option byte).
Hypothesis HM1 : forall x, 0 <= x < 2^64 -> ~ (SP - 64 <= x < SP) -> ~ (buf + 8 <= x < buf + 12) -> ~ (buf + 16 <= x < buf + 24) -> m1 (wa x) = m0 (wa x).
Hypothesis HG1 : mem_grows m0 m1.
Hypothesis Hb0 : bot < bp0.

Definition KLOOP : list nat := [1; 2; 3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Ltac kin Hk := clear -Hk; cbn [KLOOP In] in Hk; repeat (destruct Hk as [<-|Hk]; [cbn [In]; memb|]); destruct Hk.
Definition MEMI (m : word -> option byte) (sz : Z) : Prop :=
  (forall x, 0 <= x < 2^64 -> ~ (buf + 8 <= x < buf + 12) -> ~ (buf + 16 <= x < buf + 256) -> m (wa x) = m1 (wa x)) /\
  mem_grows m1 m /\ rd m (buf + 8) 4 sz.
Definition LI (m : word -> option byte) (R : bvmap 5 word) (bp sz : Z) : Prop :=
  getr R 8 = wa 30 /\ getr R 9 = wa (top - 16) /\ getr R 10 = wa buf /\ getr R 11 = wa pc /\ getr R 12 = wa bp /\
  getr R 13 = wa 4096 /\ getr R 14 = wa (buf + 16) /\ getr R 15 = wa sz /\
  (forall k, In k KLOOP -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr R1 (Z_to_bv 5 (Z.of_nat k))) /\
  1 <= sz <= 30 /\ bot < bp /\ bp < top - 16 /\ bp mod 8 = 0 /\ bp0 <= bp /\ MEMI m sz.
Definition LX (m : word -> option byte) (R : bvmap 5 word) (sz : Z) : Prop :=
  (forall k, In k KLOOP -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr R1 (Z_to_bv 5 (Z.of_nat k))) /\ 1 <= sz <= 30 /\ MEMI m sz.

#[using="pc bp0 HSP Hbuf Hpc Hbp0 HM1"] Lemma memi_m0 : forall m sz x, MEMI m sz -> 0 <= x < 2^64 -> ~ WUW x -> m (wa x) = m0 (wa x).
Proof. LiaFast.lf_pins (fun (pc bp0 HSP Hbuf Hpc Hbp0 HM1 : LiaFast.U) => LiaFast.u0).
  intros m sz x (Hm & _ & _) Hx Hw. unfold WUW in Hw. rewrite (Hm x Hx) by slia. apply HM1; slia.
Qed.

#[using="SP HSP Hbuf HWB Htb Hpc Hbp0 Hbp0b HM1 HG1 Hb0"] Lemma uw_loop : forall j bp sz m R, Z.to_nat (top - bp) = j -> uch bp -> LI m R bp sz ->
  exists R' m' sz', msteps SEGS (mkst R (wa 0x829d4) m rom) (mkst R' (wa 0x82a10) m' rom) /\ LX m' R' sz'.
Proof. LiaFast.lf_pins (fun (SP HSP Hbuf HWB Htb Hpc Hbp0 Hbp0b HM1 HG1 Hb0 : LiaFast.U) => LiaFast.u0).
  intros j. induction j as [j IH] using lt_wf_ind. intros bp sz m R Hj HU HL.
  destruct HL as (L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & LK & Hsz & Hb1 & Hb2 & Hb3 & Hb4 & HMI).
  pose proof (Hbp0b Hb0) as Hbb.
  inversion HU as [bp' Hr8 Hr16 Hnext Hbp']. subst bp'.
  destruct Hr8 as (bs1 & Hbs1). destruct Hr16 as (bs2 & Hbs2).
  destruct (rd_some _ _ _ Hbs1) as (w1 & Hw1 & Rw1). destruct (rd_some _ _ _ Hbs2) as (nb & Hnb & Rnb).
  pose proof Rnb as Rnb0.
  assert (Hrd_m : forall a, bp - 16 <= a <= bp - 8 -> rdn SEGS m (wa a) 8 = rdn SEGS m0 (wa a) 8).
  { intros a Ha. apply rdn_frame; [clear -Ha Hb4 Hbb Hbuf HSP; slia | clear -Ha Hb2 Htb; assert (X1 : a + Z.of_nat 8 <= 2^47) by slia; eapply Z.le_trans; [exact X1 | apply Z.pow_le_mono_r; slia] |]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply (memi_m0 m sz x HMI); [clear -Hx Ha Hb2 Htb Hb4 Hbb Hbuf HSP; slia|]. unfold WUW. clear -Hx Ha Hb4 Hbb Hbuf HSP. slia. }
  rewrite <- (Hrd_m (bp - 8)) in Rw1 by slia. rewrite <- (Hrd_m (bp - 16)) in Rnb by slia.
  destruct HMI as (HMm & HMg & HMsz).
  assert (Hg0 : mem_grows m0 m) by exact (mem_grows_trans _ _ _ HG1 HMg).
  assert (P : AXF_uwlz.uwl_pre R m buf pc bp sz (top - 16) w1 nb).
  { constructor; try assumption; try slia.
    all: first [ (replace (bp + -8) with (bp - 8) by slia; exact Rw1) | (replace (bp + -16) with (bp - 16) by slia; exact Rnb)
               | (intros d k Hd Hk; apply (store_ok_mono SEGS k m0 m); [exact Hg0|];
                  first [apply HWB; slia | (replace (buf + 8 * sz + 16 + d) with (buf + 8 + (8 * sz + 8 + d)) by slia; apply HWB; slia)]) ]. }
  assert (KLs : forall k, In k KLOOP -> In k [1; 2; 3; 4; 5; 6; 7; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat) by (intros k Hk; cbn [KLOOP In] in Hk; repeat (destruct Hk as [<-|Hk]; [memb|]); destruct Hk).
  assert (KLs2 : forall k, In k KLOOP -> In k [1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat) by (intros k Hk; cbn [KLOOP In] in Hk; repeat (destruct Hk as [<-|Hk]; [memb|]); destruct Hk).
  assert (KLs3 : forall k, In k KLOOP -> In k [1; 2; 3; 4; 5; 6; 7; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat) by (intros k Hk; cbn [KLOOP In] in Hk; repeat (destruct Hk as [<-|Hk]; [memb|]); destruct Hk).
  assert (MX0 : MEMI m sz) by exact (conj HMm (conj HMg HMsz)).
  (* [comment removed for export] *)
  assert (MXA : sz < 30 -> MEMI (wbytes (wbytes m (wa (buf + 8)) (word_to_le_bytes 4 (wa (sz + 1)))) (wa (buf + 8 * sz + 16)) (word_to_le_bytes 8 (wa w1))) (sz + 1)).
  { intros Hs. split; [|split].
    - intros x Hx H1 H2. rewrite wb_other by (lenb; slia). rewrite wb_other by (lenb; slia). exact (HMm x Hx H1 H2).
    - eapply mem_grows_trans; [exact HMg|]. eapply mem_grows_trans; apply wbytes_grows.
    - srdwb. }
  destruct (Z_le_gt_dec 30 sz) as [Hs30|Hs30].
  { destruct (AXF_uwlz.uwl_puwl1 R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & K8 & _ & _ & _ & _ & _ & _ & _ & K).
    { apply sc_l1; slia. }
    exists R', m, sz. split; [exact Hms|]. split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia | exact MX0]. }
  destruct (Z_lt_ge_dec w1 4096) as [Hw4|Hw4].
  { destruct (AXF_uwlz.uwl_puwl2 R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & K).
    { apply sc_l2; slia. }
    lastK K.
    exists R', m, sz. split; [exact Hms|]. split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia | exact MX0]. }
  assert (Hal : forall z, 0 <= z < 2^64 -> Z.land z 7 = z mod 8) by (intros z Hz; change 7 with (Z.ones 3); rewrite Z.land_ones by slia; reflexivity).
  destruct (Z.eq_dec w1 pc) as [Hwp|Hwp].
  - (* [comment removed for export] *)
    destruct (Z_le_gt_dec nb bp) as [Hn1|Hn1].
    { destruct (AXF_uwlz.uwl_puwlk3 R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & K).
      { apply sc_k3; slia. }
      lastK K.
      exists R', m, sz. split; [exact Hms|]. split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia | exact MX0]. }
    destruct (Z_le_gt_dec (top - 16) nb) as [Hn2|Hn2].
    { destruct (AXF_uwlz.uwl_puwlk4 R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & K).
      { apply sc_k4; slia. }
      lastK K.
      exists R', m, sz. split; [exact Hms|]. split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia | exact MX0]. }
    destruct (Z.eq_dec (nb mod 8) 0) as [Hn3|Hn3].
    + destruct (AXF_uwlz.uwl_puwlkc R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & L8' & L9' & L10' & L11' & L12' & L13' & L14' & L15' & _ & _ & K).
      { apply sc_kc; slia. }
      destruct (IH (Z.to_nat (top - nb)) ltac:(slia) nb sz m R' eq_refl (Hnext nb Rnb0 ltac:(slia) ltac:(slia) Hn3)) as (R2 & m2 & sz2 & Hms2 & HX).
      { refine (conj L8' (conj L9' (conj L10' (conj L11' (conj L12' (conj L13' (conj L14' (conj L15' _)))))))).
        split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia|]. split; [slia|]. split; [slia|]. split; [exact Hn3|]. split; [slia | exact MX0]. }
      exists R2, m2, sz2. split; [exact (msteps_trans SEGS _ _ _ Hms Hms2) | exact HX].
    + destruct (AXF_uwlz.uwl_puwlk5 R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & K).
      { apply sc_k5; slia. }
      lastK K.
      exists R', m, sz. split; [exact Hms|]. split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia | exact MX0].
  - (* [comment removed for export] *)
    pose proof (MXA ltac:(slia)) as MX1.
    destruct (Z_le_gt_dec nb bp) as [Hn1|Hn1].
    { destruct (AXF_uwlz.uwl_puwls3 R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & K).
      { apply sc_s3; slia. }
      lastK K.
      exists R', (AXF_uwlz.uwl_mem_puwls3 m R buf pc bp sz (top - 16) w1 nb), (sz + 1). split; [exact Hms|]. split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia | exact MX1]. }
    destruct (Z_le_gt_dec (top - 16) nb) as [Hn2|Hn2].
    { destruct (AXF_uwlz.uwl_puwls4 R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & K).
      { apply sc_s4; slia. }
      lastK K.
      exists R', (AXF_uwlz.uwl_mem_puwls4 m R buf pc bp sz (top - 16) w1 nb), (sz + 1). split; [exact Hms|]. split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia | exact MX1]. }
    destruct (Z.eq_dec (nb mod 8) 0) as [Hn3|Hn3].
    + destruct (AXF_uwlz.uwl_puwlsc R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & L8' & L9' & L10' & L11' & L12' & L13' & L14' & L15' & _ & _ & K).
      { apply sc_sc; slia. }
      destruct (IH (Z.to_nat (top - nb)) ltac:(slia) nb (sz + 1) (AXF_uwlz.uwl_mem_puwlsc m R buf pc bp sz (top - 16) w1 nb) R' eq_refl (Hnext nb Rnb0 ltac:(slia) ltac:(slia) Hn3)) as (R2 & m2 & sz2 & Hms2 & HX).
      { refine (conj L8' (conj L9' (conj L10' (conj L11' (conj L12' (conj L13' (conj L14' (conj L15' _)))))))).
        split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia|]. split; [slia|]. split; [slia|]. split; [exact Hn3|]. split; [slia | exact MX1]. }
      exists R2, m2, sz2. split; [exact (msteps_trans SEGS _ _ _ Hms Hms2) | exact HX].
    + destruct (AXF_uwlz.uwl_puwls5 R m rom buf pc bp sz (top - 16) w1 nb P) as (R' & Hms & K).
      { apply sc_s5; slia. }
      lastK K.
      exists R', (AXF_uwlz.uwl_mem_puwls5 m R buf pc bp sz (top - 16) w1 nb), (sz + 1). split; [exact Hms|]. split; [intros k Hk; rewrite (K k ltac:(kin Hk)); exact (LK k Hk)|]. split; [slia | exact MX1].
Qed.
End LOOP.

(* [comment removed for export] *)
#[using="buf pc bp0 HR2 HSP Hbuf Hpc Hbp0"] Lemma uw_exit : forall R m, getr R 2 = wa (SP - 64) ->
  (forall k, In k [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
  (forall i v, In (i, v) [(56, getr regs0 1); (48, getr regs0 8); (40, getr regs0 9); (32, getr regs0 18); (24, getr regs0 19);
                        (16, getr regs0 20); (8, getr regs0 21); (0, getr regs0 22)] ->
     rdn SEGS m (wa (SP - 64 + i)) 8 = Some (word_to_le_bytes 8 v)) ->
  exists R', msteps SEGS (mkst R (wa 0x82a10) m rom) (mkst R' (wa 0x82a34) m rom) /\
    (forall k, In k KALL -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins (fun (buf pc bp0 HR2 HSP Hbuf Hpc Hbp0 : LiaFast.U) => LiaFast.u0).
  intros R m H2 HK HS.
  assert (P : AXF_uwez.uwe_pre R m (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
              (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20)) (bv_unsigned (getr regs0 21))
              (bv_unsigned (getr regs0 22))).
  { constructor; try apply u_rng.
    all: rgz; rewrite ?H2, ?u_wa_small by slia; try (pose proof HSP; slia).
    all: rewrite wa_u; apply HS; cbn [In]; memb. }
  destruct (AXF_uwez.uwe_puwe R m rom _ _ _ _ _ _ _ _ P) as (R' & Hms & K).
  { cbn [AXF_uwe.RES_puwe fst snd]. scgo. }
  exists R'. split; [exact Hms|].
  destruct K as (K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & KK).
  intros k Hk. cbn [KALL In] in Hk.
  destruct Hk as [<-|Hk]; [rgz; replace (Z_to_bv 5 (Z.of_nat 1)) with (@BV 5 1 I) by (apply bv_eq; reflexivity); rewrite K1; apply wa_u|].
  destruct Hk as [<-|Hk]; [rgz; rewrite K2; rewrite H2, HR2, u_wa_small by slia; f_equal; slia|].
  destruct Hk as [<-|Hk]; [rewrite (KK 3%nat ltac:(cbn [In]; memb)); apply HK; cbn [In]; memb|].
  destruct Hk as [<-|Hk]; [rewrite (KK 4%nat ltac:(cbn [In]; memb)); apply HK; cbn [In]; memb|].
  destruct Hk as [<-|Hk]; [replace (Z_to_bv 5 (Z.of_nat 8)) with (@BV 5 8 I) by (apply bv_eq; reflexivity); rewrite K8; apply wa_u|].
  destruct Hk as [<-|Hk]; [replace (Z_to_bv 5 (Z.of_nat 9)) with (@BV 5 9 I) by (apply bv_eq; reflexivity); rewrite K9; apply wa_u|].
  destruct Hk as [<-|Hk]; [replace (Z_to_bv 5 (Z.of_nat 18)) with (@BV 5 18 I) by (apply bv_eq; reflexivity); rewrite K18; apply wa_u|].
  destruct Hk as [<-|Hk]; [replace (Z_to_bv 5 (Z.of_nat 19)) with (@BV 5 19 I) by (apply bv_eq; reflexivity); rewrite K19; apply wa_u|].
  destruct Hk as [<-|Hk]; [replace (Z_to_bv 5 (Z.of_nat 20)) with (@BV 5 20 I) by (apply bv_eq; reflexivity); rewrite K20; apply wa_u|].
  destruct Hk as [<-|Hk]; [replace (Z_to_bv 5 (Z.of_nat 21)) with (@BV 5 21 I) by (apply bv_eq; reflexivity); rewrite K21; apply wa_u|].
  destruct Hk as [<-|Hk]; [replace (Z_to_bv 5 (Z.of_nat 22)) with (@BV 5 22 I) by (apply bv_eq; reflexivity); rewrite K22; apply wa_u|].
  repeat (destruct Hk as [<-|Hk]; [match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KK k ltac:(cbn [In]; memb)); apply HK; cbn [In]; memb end|]).
  destruct Hk.
Qed.
(* [comment removed for export] *)
Definition M1 : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m0
    (wa (SP + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat 1)))))))
    (wa (SP + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat 8)))))))
    (wa (SP + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat 9)))))))
    (wa (SP + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat 18)))))))
    (wa (SP + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat 19)))))))
    (wa (SP + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat 20)))))))
    (wa (SP + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat 21)))))))
    (wa (SP + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat 22)))))))
    (wa (buf + 8)) (word_to_le_bytes 4 (wa 1))) (wa (buf + 16)) (word_to_le_bytes 8 (wa pc)).

#[using="HSP Hbuf"] Lemma M1_out : forall x, 0 <= x < 2^64 -> ~ (SP - 64 <= x < SP) -> ~ (buf + 8 <= x < buf + 12) -> ~ (buf + 16 <= x < buf + 24) -> M1 (wa x) = m0 (wa x).
Proof. LiaFast.lf_pins (fun (HSP Hbuf : LiaFast.U) => LiaFast.u0).
  intros x Hx H1 H2 H3. assert (HR : 2^22 <= SP <= 2^47 /\ SP <= buf /\ buf + 2056 <= 2^47) by (clear - HSP Hbuf; lia).
  unfold M1. repeat (rewrite wb_other by (lenb; clear - HR Hx H1 H2 H3; lia)). reflexivity.
Qed.
#[using="Type"] Lemma M1_grows : mem_grows m0 M1.
Proof. LiaFast.lf_pins LiaFast.u0. unfold M1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
#[using="HSP Hbuf"] Lemma M1_saves : forall i v, In (i, v) [(56, getr regs0 1); (48, getr regs0 8); (40, getr regs0 9); (32, getr regs0 18); (24, getr regs0 19);
                        (16, getr regs0 20); (8, getr regs0 21); (0, getr regs0 22)] ->
  forall m, (forall x, 0 <= x < 2^64 -> ~ (buf + 8 <= x < buf + 12) -> ~ (buf + 16 <= x < buf + 256) -> m (wa x) = M1 (wa x)) ->
  rdn SEGS m (wa (SP - 64 + i)) 8 = Some (word_to_le_bytes 8 v).
Proof. LiaFast.lf_pins (fun (HSP Hbuf : LiaFast.U) => LiaFast.u0).
  intros i v Hi m Hm. cbn [In] in Hi.
  assert (HR : 2^22 <= SP <= 2^47 /\ SP <= buf /\ buf + 2056 <= 2^47) by (clear - HSP Hbuf; lia).
  assert (Hrd : forall j, 0 <= j <= 56 -> rdn SEGS m (wa (SP - 64 + j)) 8 = rdn SEGS M1 (wa (SP - 64 + j)) 8).
  { intros j Hj. apply rdn_frame; [clear - HR Hj; lia | zn; clear - HR Hj; lia|]. intros x Hx. zn. apply Hm; clear - HR Hj Hx; lia. }
  clear Hm.
  Ltac rdq HR := repeat first [ (apply wb_rd_hit; [clear; lia | clear - HR; lia | zn; clear - HR; lia])
                             | (apply wb_rd_other; [clear - HR; lia | zn; clear - HR; lia | clear - HR; lia | lenb; clear - HR; lia | lenb; clear - HR; lia | ]) ].
  repeat (destruct Hi as [Hi|Hi]; [injection Hi as <- <-; rewrite Hrd by (clear; lia);
     rewrite <- (wa_u (getr regs0 _));
     match goal with |- rdn SEGS ?mm (wa ?a) 8 = Some (word_to_le_bytes 8 (wa ?z)) => change (rd mm a 8 z) end;
     match goal with |- rd _ (SP - 64 + ?j) _ _ => replace (SP - 64 + j) with (SP + (j - 64)) by (clear; lia); cbn [Z.sub Z.add Z.opp Pos.sub_mask] end;
     unfold M1; rdq HR|]); try destruct Hi.
Qed.

(* [comment removed for export] *)
#[using="pc bp0 top bot HR2 HR10 HR11 HR12 HR13 HR14 HR15 HSP HSTK Hbuf HWB HGOT HPSZ HIMG Htb Hpc Hbp0 HCH Hbp0b"] Theorem uw_contract : exists R' m' sz, msteps SEGS (mkst regs0 (wa 0x82914) m0 rom) (mkst R' (wa 0x82a34) m' rom) /\
  (forall k, In k KALL -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) /\
  1 <= sz <= 30 /\ rd m' (buf + 8) 4 sz /\
  (forall x, 0 <= x < 2^64 -> ~ WUW x -> m' (wa x) = m0 (wa x)) /\ mem_grows m0 m'.
Proof. LiaFast.lf_pins (fun (pc bp0 top bot HR2 HR10 HR11 HR12 HR13 HR14 HR15 HSP HSTK Hbuf HWB HGOT HPSZ HIMG Htb Hpc Hbp0 HCH Hbp0b : LiaFast.U) => LiaFast.u0).
  assert (P : AXF_uw0z.uw0_pre regs0 m0 buf pc bp0 top bot 4096).
  { constructor; try assumption; try slia.
    all: rgz; rewrite ?HR2, ?u_wa_small by slia; try slia; try exact HSTK.
    all: first [ (intros d k Hd Hk; apply HWB; slia) | exact HGOT | exact HPSZ | exact HIMG ]. }
  assert (EM : forall mm, mm = M1 -> (forall x, 0 <= x < 2^64 -> ~ (buf + 8 <= x < buf + 12) -> ~ (buf + 16 <= x < buf + 256) -> mm (wa x) = M1 (wa x))).
  { intros mm -> x _ _ _. reflexivity. }
  assert (Hsh : Z.shiftr top 12 <> 0).
  { intros Hc. pose proof (Z.shiftr_div_pow2 top 12 ltac:(slia)) as E. rewrite Hc in E. assert (top / 2^12 >= 1) by (apply Z.le_ge, Z.div_le_lower_bound; slia). slia. }
  assert (XIT : forall R, getr R 2 = wa (SP + -64) ->
            (forall k, In k [1; 3; 4; 5; 6; 7; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
            exists R' m' sz, msteps SEGS (mkst R (wa 0x82a10) M1 rom) (mkst R' (wa 0x82a34) m' rom) /\
              (forall k, In k KALL -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) /\
              1 <= sz <= 30 /\ rd m' (buf + 8) 4 sz /\ (forall x, 0 <= x < 2^64 -> ~ WUW x -> m' (wa x) = m0 (wa x)) /\ mem_grows m0 m').
  { intros R H2 HK. destruct (uw_exit R M1 ltac:(rewrite H2; f_equal; slia) ltac:(intros k Hk; apply HK; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [memb|]); destruct Hk)
                               (fun i v Hi => M1_saves i v Hi M1 (EM M1 eq_refl))) as (R' & Hms & HK').
    exists R', M1, 1. split; [exact Hms|]. split; [exact HK'|]. split; [slia|]. split; [unfold M1; srdwb|].
    split; [intros x Hx Hw; unfold WUW in Hw; apply M1_out; slia | exact M1_grows]. }
  assert (Hshb : forall G : Prop, (negb (Z.shiftr top 12 =? 0) = true -> G) -> (negb ((top mod 2^64) ≫ (12 mod 64) mod 2^64 =? 0 mod 2^64) = true -> G)).
  { intros G HG H. apply HG. rewrite (Z.mod_small top (2^64)) in H by slia. change (12 mod 64) with 12 in H. change (0 mod 2^64) with 0 in H.
    rewrite Z.mod_small in H; [exact H|]. split; [apply Z.shiftr_nonneg; slia | rewrite Z.shiftr_div_pow2 by slia; apply Z.div_lt_upper_bound; slia]. }
  assert (Hshg : negb ((top mod 2^64) ≫ (12 mod 64) mod 2^64 =? 0 mod 2^64) = true).
  { rewrite (Z.mod_small top (2^64)) by slia. change (12 mod 64) with 12. change (0 mod 2^64) with 0.
    rewrite Z.mod_small; [apply negb_true_iff, Z.eqb_neq; exact Hsh|]. split; [apply Z.shiftr_nonneg; slia | rewrite Z.shiftr_div_pow2 by slia; apply Z.div_lt_upper_bound; slia]. }
  destruct (Z_le_gt_dec bp0 bot) as [Hq1|Hq1].
  { destruct (AXF_uw0z.uw0_puw0b regs0 m0 rom buf pc bp0 top bot 4096 P) as (R & Hms & K).
    { exact (sc0b regs0 m0 buf pc bp0 top bot ltac:(clear - Hpc Hbp0 Htb Hbuf HSP; slia) Hshg Hq1). }
    assert (EQM : AXF_uw0z.uw0_mem_puw0b m0 regs0 buf pc bp0 top bot 4096 = M1) by (unfold AXF_uw0z.uw0_mem_puw0b, M1; rgz; rewrite HR2, u_wa_small by slia; reflexivity).
    rewrite EQM in Hms. destruct K as (K2 & KK). lastK KK.
    destruct (XIT R ltac:(rewrite K2; rgz; rewrite HR2, u_wa_small by slia; reflexivity) KK) as (R' & m' & sz & Hms' & X).
    exists R', m', sz. split; [exact (msteps_trans SEGS _ _ _ Hms Hms') | exact X]. }
  destruct (Z_le_gt_dec (top - 16) bp0) as [Hq2|Hq2].
  { destruct (AXF_uw0z.uw0_puw0c regs0 m0 rom buf pc bp0 top bot 4096 P) as (R & Hms & K).
    { exact (sc0c regs0 m0 buf pc bp0 top bot ltac:(clear - Hpc Hbp0 Htb Hbuf HSP; slia) Hshg ltac:(clear - Hq1; slia) Hq2). }
    assert (EQM : AXF_uw0z.uw0_mem_puw0c m0 regs0 buf pc bp0 top bot 4096 = M1) by (unfold AXF_uw0z.uw0_mem_puw0c, M1; rgz; rewrite HR2, u_wa_small by slia; reflexivity).
    rewrite EQM in Hms. destruct K as (K2 & KK). lastK KK.
    destruct (XIT R ltac:(rewrite K2; rgz; rewrite HR2, u_wa_small by slia; reflexivity) KK) as (R' & m' & sz & Hms' & X).
    exists R', m', sz. split; [exact (msteps_trans SEGS _ _ _ Hms Hms') | exact X]. }
  assert (Hal : Z.land bp0 7 = bp0 mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by slia; reflexivity).
  assert (Hm8 : 0 <= bp0 mod 8 < 8) by (apply Z.mod_pos_bound; slia).

  destruct (Z.eq_dec (bp0 mod 8) 0) as [Hq3|Hq3].
  2: { destruct (AXF_uw0z.uw0_puw0d regs0 m0 rom buf pc bp0 top bot 4096 P) as (R & Hms & K).
       { exact (sc0d regs0 m0 buf pc bp0 top bot ltac:(clear - Hpc Hbp0 Htb Hbuf HSP; slia) Hshg ltac:(clear - Hq1; slia) ltac:(clear - Hq2; slia) Hq3). }
       assert (EQM : AXF_uw0z.uw0_mem_puw0d m0 regs0 buf pc bp0 top bot 4096 = M1) by (unfold AXF_uw0z.uw0_mem_puw0d, M1; rgz; rewrite HR2, u_wa_small by slia; reflexivity).
       rewrite EQM in Hms. destruct K as (K2 & KK). lastK KK.
       destruct (XIT R ltac:(rewrite K2; rgz; rewrite HR2, u_wa_small by slia; reflexivity) KK) as (R' & m' & sz & Hms' & X).
       exists R', m', sz. split; [exact (msteps_trans SEGS _ _ _ Hms Hms') | exact X]. }
  (* [comment removed for export] *)
  destruct (AXF_uw0z.uw0_puw0a regs0 m0 rom buf pc bp0 top bot 4096 P) as (R & Hms & K).
  { exact (sc0a regs0 m0 buf pc bp0 top bot ltac:(clear - Hpc Hbp0 Htb Hbuf HSP; slia) Hshg ltac:(clear - Hq1; slia) ltac:(clear - Hq2; slia) Hq3). }
  assert (EQM : AXF_uw0z.uw0_mem_puw0a m0 regs0 buf pc bp0 top bot 4096 = M1) by (unfold AXF_uw0z.uw0_mem_puw0a, M1; rgz; rewrite HR2, u_wa_small by slia; reflexivity).
  rewrite EQM in Hms.
  destruct K as (K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & _ & _ & KK).
  assert (LI0 : LI R M1 M1 R bp0 1).
  { refine (conj K8 (conj K9 (conj K10 (conj K11 (conj K12 (conj K13 (conj K14 (conj K15 _)))))))).
    split; [intros k Hk; reflexivity|]. split; [slia|]. split; [slia|]. split; [slia|]. split; [exact Hq3|]. split; [slia|].
    split; [intros x _ _ _; reflexivity|]. split; [apply mem_grows_refl|]. unfold M1; srdwb. }
  destruct (uw_loop R M1 M1_out M1_grows ltac:(slia) (Z.to_nat (top - bp0)) bp0 1 M1 R eq_refl (HCH ltac:(slia)) LI0) as (R2 & m2 & sz2 & Hms2 & LK2 & Hsz2 & HMI2).
  destruct HMI2 as (HM2 & HG2 & HS2).
  destruct (uw_exit R2 m2 ltac:(transitivity (getr R2 (Z_to_bv 5 (Z.of_nat 2))); [f_equal; apply bv_eq; reflexivity|];
                                rewrite (LK2 2%nat ltac:(cbn; memb)); rgz; rewrite K2, HR2, u_wa_small by slia; f_equal; slia)
              ltac:(intros k Hk; rewrite (LK2 k ltac:(cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [cbn [KLOOP In]; memb|]); destruct Hk));
                    apply KK; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [memb|]); destruct Hk)
              (fun i v Hi => M1_saves i v Hi m2 HM2)) as (R3 & Hms3 & HK3).
  exists R3, m2, sz2. split; [exact (msteps_trans SEGS _ _ _ Hms (msteps_trans SEGS _ _ _ Hms2 Hms3))|].
  split; [exact HK3|]. split; [exact Hsz2|]. split; [exact HS2|]. split.
  - intros x Hx Hw. unfold WUW in Hw. rewrite (HM2 x Hx) by slia. apply M1_out; slia.
  - exact (mem_grows_trans _ _ _ M1_grows HG2).
Qed.
End UW.
End AXG_uw.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AXG_uw.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg AcComm AcDenW AcHand.

Module AXG_put4.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import RefMemcpyLib SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan AXG_put AXG_put2 AXG_put3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac is_arith T := lazymatch T with
  | @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac | Nat.le _ _ => idtac | Nat.lt _ _ => idtac | le _ _ => idtac | lt _ _ => idtac
  | ?A /\ ?B => is_arith A; is_arith B
  | ?A \/ ?B => is_arith A; is_arith B
  | ~ ?A => is_arith A
  | True => idtac | False => idtac
  end.
Ltac prune_ctx := repeat match goal with
  | H : ?T |- _ => lazymatch type of T with
                   | Prop => tryif is_arith T then fail else clear H
                   | _ => fail
                   end
  end.
Ltac prune_mod := lazymatch goal with
  | |- context [Z.modulo _ _] => idtac
  | |- context [Z.div _ _] => idtac
  | _ => repeat match goal with
              | H : Z.modulo _ _ = _ |- _ => clear H
              | H : context [Z.modulo _ _] |- _ => lazymatch type of H with _ /\ _ => let H1 := fresh "C" in let H2 := fresh "C" in pose proof H as [H1 H2]; clear H end
              end
  end.
Ltac slia := first [ LiaFast.lia_fast_tiers | (prune_ctx; prune_mod; lia) ].
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Lemma grows_wb : forall m m' a bs, mem_grows m m' -> mem_grows m (wbytes m' a bs).
Proof. intros m m' a bs H. eapply mem_grows_trans; [exact H | apply wbytes_grows]. Qed.
Ltac growsc := repeat apply grows_wb; apply mem_grows_refl.

(* [comment removed for export] *)
Lemma wb_rd_hit_s : forall m SP c w v, (1 <= w <= 8)%nat -> 2^20 <= SP <= 2^47 -> 0 <= c <= 8192 ->
  rd (wbytes m (wa (SP - c)) (word_to_le_bytes w (wa v))) (SP - c) w v.
Proof. intros m SP c w v Hw HS Hc. apply wb_rd_hit; lia. Qed.
Lemma wb_rd_other_s : forall m SP c w v c' bs, 2^20 <= SP <= 2^47 -> 0 <= c <= 8192 -> (w <= 8)%nat -> 0 <= c' <= 8192 ->
  (length bs <= 8)%nat -> (c' + Z.of_nat w <= c \/ c + Z.of_nat (length bs) <= c') -> rd m (SP - c) w v -> rd (wbytes m (wa (SP - c')) bs) (SP - c) w v.
Proof. intros m SP c w v c' bs HS Hc Hw Hc' Hl Hd H. apply wb_rd_other; [lia | lia | lia | lia | lia | exact H]. Qed.
Ltac rrs HS H := repeat first [
    lazymatch goal with
    | |- rd (wbytes _ (wa (?S - _)) _) (?S - _) _ _ =>
        first [ (apply wb_rd_hit_s; [clear; lia | exact HS | clear; lia])
              | (apply wb_rd_other_s; [exact HS | clear; lia | clear; lia | clear; lia | lenb; clear; lia | lenb; clear; lia | ]) ]
    end
  | (apply wb_rd_hit; [clear; lia | clear - H; lia | zn; clear - H; lia])
  | (apply wb_rd_other; [clear - H; lia | zn; clear - H; lia | clear - H; lia | lenb; clear - H; lia | lenb; clear - H; lia | ]) ].

Lemma shiftr_small : forall x k, 0 <= x < 2^k -> 0 <= k -> Z.shiftr x k = 0.
Proof. intros x k H Hk. rewrite Z.shiftr_div_pow2 by slia. apply Z.div_small. slia. Qed.
Lemma land_ones16 : forall x, 0 <= x < 65536 -> Z.land x 65535 = x.
Proof. intros x H. change 65535 with (Z.ones 16). rewrite Z.land_ones by slia. apply Z.mod_small. slia. Qed.
Lemma blk_off : forall F, 0 <= F < 2^20 -> Z.shiftr ((17592186044416 * F) mod 2^64) 41 = 8 * F.
Proof.
  intros F HF. rewrite Z.mod_small by slia. rewrite Z.shiftr_div_pow2 by slia.
  change (2^41) with 2199023255552. replace (17592186044416 * F) with ((8 * F) * 2199023255552) by ring. rewrite Z.div_mul by slia. reflexivity.
Qed.

Lemma stk_ok_move : forall m SP s K, 0 <= SP < 2^64 -> 0 <= s < 2^64 -> stk_ok SEGS m (wa SP) 2048 ->
  SP - 2048 <= s - K -> s <= SP -> 0 <= K -> stk_ok SEGS m (wa s) K.
Proof.
  intros m SP s K H1 H2 H H3 H4 H5 a k A1 A2. apply H; rewrite u_wa_small in * by slia; slia.
Qed.

Lemma wr_owned : forall m m' D1 B1 n F st a k, INV_D m D1 B1 n F st -> mem_grows m m' ->
  0 <= a -> a + Z.of_nat k <= 2^64 -> (forall x, a <= x < a + Z.of_nat k -> downed D1 B1 x) -> store_ok SEGS m' (wa a) k = true.
Proof.
  intros m m' D1 B1 n F st a k I G Ha Hk Hall. destruct k as [|k']; [reflexivity|]. rewrite Nat2Z.inj_succ in Hk.
  apply store_ok_of_all; [rewrite Nat2Z.inj_succ, u_wa_small by slia; slia|].
  intros x Hx. rewrite <- (wa_u x). rewrite Nat2Z.inj_succ, u_wa_small in Hx by slia.
  apply (wview_grows m m' _ G). apply (d_wr _ _ _ _ _ _ I). apply Hall. slia.
Qed.

(* [comment removed for export] *)
Lemma put_lock : forall {fx : FPState} rom m m1 R SP b hd D1 B1 n F st,
  INV_D m D1 B1 n F st -> 2^46 <= SP <= 2^47 -> SP mod 16 = 0 -> stk_ok SEGS m (wa SP) 2048 -> mem_grows m m1 ->
  (forall x, 0 <= x < 2^64 -> ~ (SP - 112 <= x < SP) -> m1 (wa x) = m (wa x)) ->
  0 <= b < 1048576 -> 0 <= hd < 2^31 -> rd m (TAB + 4 * b) 4 hd ->
  getr R (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 112) -> getr R (Z_to_bv 5 (Z.of_nat 18)) = wa (TAB + 4 * b) ->
  getr R (Z_to_bv 5 (Z.of_nat 25)) = wa hd ->
  exists R6 m2, msteps SEGS (mkst R (wa 0x82120) m1 rom) (mkst R6 (wa 0x82158) m2 rom) /\
    getr R6 (Z_to_bv 5 (Z.of_nat 21)) = wa hd /\
    (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat ->
       getr R6 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 152 <= x < SP - 112) -> ~ (TAB + 4 * b <= x < TAB + 4 * b + 4) -> m2 (wa x) = m1 (wa x)) /\
    mem_grows m1 m2.
Proof.
  intros fx rom m m1 R SP b hd D1 B1 n F st I HSP HSPa HSTK G1 HM1 Hb Hhd Rhd R2 R18 R25.
  assert (P1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_plz.pl_pre R m1 hd).
  { constructor; [regzG; exact R25 | | slia | | | | | | | ].
    all: regzG; rewrite ?R2, ?R18, ?u_wa_small by slia.
    - apply (stk_ok_grows SEGS m m1 _ _ (stk_ok_move m SP (SP - 112) 1024 ltac:(slia) ltac:(slia) HSTK ltac:(slia) ltac:(slia) ltac:(slia)) G1).
    - clear - HSP. slia.
    - clear - HSP HSPa. rewrite Zminus_mod, HSPa. reflexivity.
    - clear - Hb. slia.
    - rewrite Z.add_mod by slia. rewrite Z.mul_comm, Z.mod_mul by slia. reflexivity.
    - rewrite Z.add_0_r. apply (rd_frame m m1); [slia | zn; slia | | exact Rhd]. intros x Hx. zn. apply HM1; clear - Hx Hb HSP; slia.
    - intros d k Hd Hk. apply (wr_owned m m1 D1 B1 n F st _ _ I G1); [clear - Hb Hd; slia | clear - Hb Hd Hk; slia|].
      intros x Hx. unfold downed. clear - Hx Hb Hd Hk. slia.
    - clear - Hb HSP. slia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_plz.pl_ppl R m1 rom hd P1) as (R6 & Hms6 & A1 & A10 & A11 & A12 & A13 & A14 & A21 & A25 & K6).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pl.RES_ppl fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    - apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot]. rewrite (zatom R (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_plz.VALS_pl hd) 32 hd eq_refl eq_refl) by slia.
      rewrite ext_Z_lo32_small by slia. rewrite !Z.mod_small by slia. apply Z.eqb_refl.
    - apply sc_br_z. cbn [zeval edenot]. rewrite (zatom R (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_plz.VALS_pl hd) 32 hd eq_refl eq_refl) by slia.
      rewrite ext_Z_lo32_small by slia. cbn [branch_taken]. unfold bv_lts, bv_signed. rewrite !u_wa_small by slia.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. apply negb_true_iff, Z.ltb_ge. change (2 ^ Z.of_N 64) with 18446744073709551616.
      change (18446744073709551616 / 2) with 9223372036854775808. rewrite !Z.mod_small by slia. slia. }
  regzH A21. rewrite ext_Z_lo32_small in A21 by slia.
  exists R6, (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_plz.pl_mem_ppl m1 R hd). split; [exact Hms6|]. split; [exact A21|]. split; [exact K6|]. split.
  - intros x Hx H1 H2. unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_plz.pl_mem_ppl. regz_all. rewrite R2, R18, !u_wa_small by slia.
    repeat (rewrite wb_other; [|clear - Hx; slia|clear - HSP Hb; slia|lenb; clear - HSP Hb; slia|lenb; clear - Hx H1 H2 HSP Hb; slia]). reflexivity.
  - unfold OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_plz.pl_mem_ppl. growsc.
Qed.

(* [comment removed for export] *)
Lemma put_id : forall {fx : FPState} rom m m2 R6 D1 B1 n F st,
  INV_D m D1 B1 n F st -> n <= 65532 -> mem_grows m m2 -> rd m2 NUNIQ 4 n ->
  getr R6 (Z_to_bv 5 (Z.of_nat 9)) = wa TAB ->
  exists R7, msteps SEGS (mkst R6 (wa 0x82158) m2 rom) (mkst R7 (wa 0x82178) (wbytes m2 (wa NUNIQ) (word_to_le_bytes 4 (wa (n + 1)))) rom) /\
    getr R7 (Z_to_bv 5 (Z.of_nat 9)) = wa (n + 1) /\ getr R7 (Z_to_bv 5 (Z.of_nat 10)) = wa (n + 1) /\
    (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
       getr R7 (Z_to_bv 5 (Z.of_nat k)) = getr R6 (Z_to_bv 5 (Z.of_nat k))).
Proof.
  intros fx rom m m2 R6 D1 B1 n F st I Hn G2 RN R9.
  assert (P2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pi0z.pi0_pre R6 m2 n).
  { constructor; [regzG; exact R9 | pose proof (d_nr _ _ _ _ _ _ I); slia | exact RN |].
    intros d k Hd Hk. apply (wr_owned m m2 D1 B1 n F st _ _ I G2); [clear - Hd; slia | clear - Hd Hk; slia|].
    intros x Hx. unfold downed. clear - Hx Hd Hk. slia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pi0z.pi0_ppi0 R6 m2 rom n P2 ltac:(constructor)) as (R7 & Hms7 & B9 & B10 & B11 & K7).
  regz_all. exists R7. split; [exact Hms7|]. split; [exact B9|]. split; [exact B10 | exact K7].
Qed.

(* [comment removed for export] *)
Lemma put_node : forall {fx : FPState} rom m m3 R7 D1 B1 n F st SP TR SZ h M4 hd b,
  INV_D m D1 B1 n F st -> n <= 65532 -> F + 31 <= 1048000 -> 2^46 <= SP <= 2^47 -> SP mod 16 = 0 ->
  stk_ok SEGS m (wa SP) 2048 -> D1 + 1048576 <= SP - 2048 -> B1 + 8388608 <= SP - 2048 ->
  1 <= TR <= 2^47 -> 1 <= SZ <= 30 -> 0 <= h < 2^64 -> 0 <= M4 < 2^64 -> 0 <= hd < 2^31 -> 0 <= b < 1048576 ->
  mem_grows m m3 ->
  (forall x, 0 <= x < 2^64 -> downed D1 B1 x -> ~ (NUNIQ <= x < NUNIQ + 4) -> ~ (TAB + 4 * b <= x < TAB + 4 * b + 4) -> m3 (wa x) = m (wa x)) ->
  rd m3 (SP - 104) 8 TR -> rd m3 (SP - 96) 8 SZ ->
  getr R7 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 112) -> getr R7 (Z_to_bv 5 (Z.of_nat 8)) = wa 0 ->
  getr R7 (Z_to_bv 5 (Z.of_nat 9)) = wa (n + 1) -> getr R7 (Z_to_bv 5 (Z.of_nat 10)) = wa (n + 1) ->
  getr R7 (Z_to_bv 5 (Z.of_nat 22)) = wa 65535 -> getr R7 (Z_to_bv 5 (Z.of_nat 23)) = wa 2147483647 ->
  getr R7 (Z_to_bv 5 (Z.of_nat 24)) = wa MAP1 -> getr R7 (Z_to_bv 5 (Z.of_nat 18)) = wa (TAB + 4 * b) ->
  getr R7 (Z_to_bv 5 (Z.of_nat 19)) = wa h -> getr R7 (Z_to_bv 5 (Z.of_nat 20)) = wa M4 -> getr R7 (Z_to_bv 5 (Z.of_nat 21)) = wa hd ->
  exists R8 m4, msteps SEGS (mkst R7 (wa 0x82178) m3 rom) (mkst R8 (wa 0x733c4) m4 rom) /\
    getr R8 (Z_to_bv 5 (Z.of_nat 1)) = wa 0x7fa24 /\ getr R8 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 208) /\
    getr R8 (Z_to_bv 5 (Z.of_nat 8)) = wa (SP - 136) /\ getr R8 (Z_to_bv 5 (Z.of_nat 9)) = wa SSF /\
    getr R8 (Z_to_bv 5 (Z.of_nat 10)) = wa (B1 + 8 * F + 8) /\ getr R8 (Z_to_bv 5 (Z.of_nat 11)) = wa TR /\
    getr R8 (Z_to_bv 5 (Z.of_nat 12)) = wa (8 * SZ) /\ getr R8 (Z_to_bv 5 (Z.of_nat 18)) = wa (SZ + 1) /\
    getr R8 (Z_to_bv 5 (Z.of_nat 19)) = wa (SP - 104) /\ getr R8 (Z_to_bv 5 (Z.of_nat 20)) = wa SZ /\
    getr R8 (Z_to_bv 5 (Z.of_nat 21)) = wa 0 /\ getr R8 (Z_to_bv 5 (Z.of_nat 23)) = wa (n + 1) /\
    (forall k, In k [3; 4; 7; 16; 17; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R8 (Z_to_bv 5 (Z.of_nat k)) = getr R7 (Z_to_bv 5 (Z.of_nat k))) /\
    rd m4 (SP - 208) 8 F /\ rd m4 (SP - 152) 8 0x81ccc /\ rd m4 (SP - 160) 8 (D1 + 16 * (n + 1)) /\ rd m4 (SP - 168) 8 (D1 + 16 * (n + 1)) /\
    rd m4 (SP - 176) 8 (TAB + 4 * b) /\ rd m4 (SP - 184) 8 h /\ rd m4 (SP - 192) 8 M4 /\ rd m4 (SP - 200) 8 hd /\
    rd m4 (SP - 120) 8 0x821b0 /\ rd m4 (SP - 128) 8 0 /\ rd m4 (SP - 136) 8 0 /\
    rd m4 (D1 + 16 * (n + 1)) 8 h /\ rd m4 SSF 8 (F + SZ + 1) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 224 <= x < SP - 112) -> ~ (D1 + 16 * (n + 1) <= x < D1 + 16 * (n + 1) + 8) ->
       ~ (SSF <= x < SSF + 8) -> ~ (B1 + 8 * F <= x < B1 + 8 * F + 8) -> m4 (wa x) = m3 (wa x)) /\
    mem_grows m3 m4.
Proof.
  intros fx rom m m3 R7 D1 B1 n F st SP TR SZ h M4 hd b I Hn HF HSP HSPa HSTK HD1 HB1 HTR HSZ Hh HM4 Hhd Hb G3 FR3 SV12 SV13
    R2 R8 R9 R10 R22 R23 R24 R18 R19 R20 R21.
  pose proof I as I0. destruct I0 as [In Inr Imap ID1 Itab IF Ist IFr IB1 IB1r Iwr Isep In0].
  destruct ID1 as (D1a & D1b & D1c). destruct IB1r as (B1a & B1b & B1c). destruct Isep as (S1 & S2 & S3). clear Itab Iwr.
  assert (Hid : Z.shiftr (n + 1) 16 = 0) by (apply shiftr_small; slia).
  assert (HF20 : Z.shiftr F 20 = 0) by (apply shiftr_small; slia).
  assert (FRO : forall a w v, rd m a w v -> 0 <= a -> a + Z.of_nat w <= 2^64 -> (forall x, a <= x < a + Z.of_nat w -> downed D1 B1 x /\ ~ (NUNIQ <= x < NUNIQ + 4) /\ ~ (TAB + 4 * b <= x < TAB + 4 * b + 4)) -> rd m3 a w v).
  { intros a w v R Ha Hw Hall. apply (rd_frame m m3); [exact Ha | exact Hw | | exact R]. intros x Hx. destruct (Hall x Hx) as (A1 & A2 & A3). apply FR3; [clear - Ha Hw Hx; slia | exact A1 | exact A2 | exact A3]. }
  assert (P3 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pi1z.pi1_pre R7 m3 (n + 1) D1 F B1 TR SZ).
  { constructor.
    - regzG. exact R8.
    - regzG. exact R9.
    - regzG. exact R10.
    - regzG. exact R22.
    - regzG. exact R23.
    - regzG. exact R24.
    - regzG. rewrite R2. exact (stk_ok_grows SEGS m m3 _ _ (stk_ok_move m SP (SP - 112) 1024 ltac:(slia) ltac:(slia) HSTK ltac:(slia) ltac:(slia) ltac:(slia)) G3).
    - clear - Hn Inr. slia.
    - clear - D1a D1b. slia.
    - clear - IFr HF. slia.
    - clear - B1a B1b. slia.
    - clear - HTR. slia.
    - clear - HSZ. slia.
    - rewrite R2, u_wa_small by slia. clear - HSP. slia.
    - rewrite R2, u_wa_small by slia. clear - HSP HSPa. rewrite Zminus_mod, HSPa. reflexivity.
    - exact D1c.
    - exact B1c.
    - rewrite Hid. slia.
    - change (0 + 6057128) with MAP1. apply FRO; [exact Imap | slia | zn; slia |]. intros x Hx. zn. unfold downed. clear - Hx Hb. split; [slia|]. split; slia.
    - rewrite land_ones16 by slia. clear - D1a D1b Hn Inr. slia.
    - intros d k Hd Hk. rewrite land_ones16 by slia. apply (wr_owned m m3 D1 B1 n F st _ _ I G3); [clear - D1a Hd Inr; slia | clear - D1a D1b Hd Hk Hn Inr; slia|].
      intros x Hx. unfold downed. clear - Hx Hd Hk D1a D1b Hn Inr. slia.
    - rewrite HF20. slia.
    - change (0 + 1797256) with SSF. apply FRO; [exact IF | slia | zn; slia |]. intros x Hx. zn. unfold downed. clear - Hx Hb. split; [slia|]. split; slia.
    - intros d k Hd Hk. apply (wr_owned m m3 D1 B1 n F st _ _ I G3); [clear - Hd; slia | clear - Hd Hk; slia|]. intros x Hx. unfold downed. clear - Hx Hd Hk. slia.
    - change (0 + 1797272) with SSD. apply FRO; [exact IB1 | slia | zn; slia |]. intros x Hx. zn. unfold downed. clear - Hx Hb. split; [slia|]. split; slia.
    - rewrite R2, u_wa_small by slia. replace (SP - 112 + 8) with (SP - 104) by slia. exact SV12.
    - rewrite R2, u_wa_small by slia. replace (SP - 112 + 16) with (SP - 96) by slia. exact SV13.
    - rewrite blk_off by slia. clear - B1a B1b IFr HF. slia.
    - intros d k Hd Hk. rewrite blk_off by slia. apply (wr_owned m m3 D1 B1 n F st _ _ I G3); [clear - B1a Hd IFr; slia | clear - B1a B1b Hd Hk IFr HF; slia|].
      intros x Hx. unfold downed. clear - Hx Hd Hk B1a B1b IFr HF. slia.
    - rewrite R2, u_wa_small, land_ones16 by slia. clear - HSP HD1 D1a Hn Inr. slia.
    - rewrite R2, u_wa_small by slia. clear - HSP. slia.
    - rewrite land_ones16 by slia. clear - S1 Hn Inr. slia.
    - rewrite R2, u_wa_small, blk_off by slia. clear - HSP HB1 B1a IFr HF. slia.
    - rewrite blk_off, land_ones16 by slia. clear - S3 D1a B1a Hn Inr IFr HF. slia.
    - rewrite blk_off by slia. clear - S2 IFr. slia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pi1z.pi1_ppi1 R7 m3 rom (n + 1) D1 F B1 TR SZ P3) as (R8' & Hms8 & C1 & C2 & C5 & C6 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & K8).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pi1.RES_ppi1 fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?(zatom R7 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pi1z.VALS_pi1 (n + 1) D1 F B1 TR SZ) 34 F eq_refl eq_refl) by slia.
    all: rewrite ?(zatom R7 (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pi1z.VALS_pi1 (n + 1) D1 F B1 TR SZ) 37 SZ eq_refl eq_refl) by slia.
    all: rewrite ?ext_Z_lo32_small, ?ext_Z_hi32_zero by slia.
    all: first [rewrite br_eq_z | rewrite br_ne_z | rewrite br_ltu_z | rewrite br_geu_z].
    all: rewrite ?(Z.mod_small F (2^64)), ?(Z.mod_small SZ (2^64)) by slia; change (32 mod 64) with 32; change (20 mod 64) with 20.
    - rewrite (shiftr_small F 32) by slia. reflexivity.
    - rewrite (Z.mod_small (F + SZ)) by slia. rewrite (shiftr_small F 20), (shiftr_small (F + SZ) 20) by slia. reflexivity.
    - apply Z.ltb_lt. rewrite !Z.mod_small by slia. slia.
    - reflexivity.
    - rewrite Z.lor_0_r. rewrite Z.mod_small by slia. apply negb_true_iff, Z.eqb_neq. slia. }
  regz_all. rewrite !ext_Z_lo32_small in * by slia.
  rewrite R2, u_wa_small in C2, C8, C19 by slia. rewrite blk_off in C10 by slia.
  set (m4 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pi1z.pi1_mem_ppi1 m3 R7 (n + 1) D1 F B1 TR SZ).
  assert (Em4 : m4 = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m3
     (wa (SP - 120)) (word_to_le_bytes 8 (wa 532912))) (wa (SP - 128)) (word_to_le_bytes 8 (wa 0)))
     (wa (D1 + 16 * (n + 1))) (word_to_le_bytes 8 (wa h))) (wa (SP - 136)) (word_to_le_bytes 8 (wa 0)))
     (wa (SP - 152)) (word_to_le_bytes 8 (wa 531660))) (wa (SP - 160)) (word_to_le_bytes 8 (wa (D1 + 16 * (n + 1)))))
     (wa (SP - 168)) (word_to_le_bytes 8 (wa (D1 + 16 * (n + 1))))) (wa (SP - 176)) (word_to_le_bytes 8 (wa (TAB + 4 * b))))
     (wa (SP - 184)) (word_to_le_bytes 8 (wa h))) (wa (SP - 192)) (word_to_le_bytes 8 (wa M4)))
     (wa (SP - 200)) (word_to_le_bytes 8 (wa hd))) (wa (SP - 208)) (word_to_le_bytes 8 (wa 0)))
     (wa (SP - 136)) (word_to_le_bytes 8 (wa 0))) (wa (SP - 216)) (word_to_le_bytes 8 (wa 522756)))
     (wa (SP - 224)) (word_to_le_bytes 8 (wa (SP - 136)))) (wa SSF) (word_to_le_bytes 8 (wa (F + SZ + 1))))
     (wa (SP - 208)) (word_to_le_bytes 8 (wa F))) (wa (B1 + 8 * F)) (word_to_le_bytes 8 (wa SZ))).
  { unfold m4, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pi1z.pi1_mem_ppi1. regz_all. rewrite R2, R18, R19, R20, R21, !u_wa_small by slia. rewrite land_ones16, blk_off, ext_Z_lo32_small by slia.
    repeat (apply (f_equal3 wbytes)); try reflexivity; first [f_equal; slia | f_equal; f_equal; f_equal; slia]. }
  exists R8', m4. split; [exact Hms8|].
  split; [exact C1|]. split; [rewrite C2; f_equal; slia|]. split; [rewrite C8; f_equal; slia|]. split; [exact C9|].
  split; [rewrite C10; f_equal; slia|]. split; [exact C11|]. split; [exact C12|]. split; [exact C18|].
  split; [rewrite C19; f_equal; slia|]. split; [exact C20|]. split; [exact C21|]. split; [exact C23|]. split; [exact K8|].
  rewrite Em4. clear Em4 m4 Hms8 K8 C1 C2 C5 C6 C8 C9 C10 C11 C12 C13 C14 C15 C18 C19 C20 C21 C22 C23 C24 P3 FRO R2 R8 R9 R10 R22 R23 R24 R18 R19 R20 R21.
  assert (Hnr : 0 <= n <= 65532) by slia. clear Inr Hn.
  Ltac rr H := repeat first [ (apply wb_rd_hit; [slia | clear - H; slia | zn; clear - H; slia])
                            | (apply wb_rd_other; [clear - H; slia | zn; clear - H; slia | clear - H; slia | lenb; clear - H; slia | lenb; clear - H; slia | ]) ].
  assert (RNG : 2^46 <= SP <= 2^47 /\ D1 + 1048576 <= SP - 2048 /\ B1 + 8388608 <= SP - 2048 /\ 6529024 <= D1 /\ 6529024 <= B1 /\
                (D1 + 1048576 <= B1 \/ B1 + 8388608 <= D1) /\ 0 <= n <= 65532 /\ 0 <= F <= 1048000 /\ F + 31 <= 1048000 /\ 1 <= SZ <= 30 /\ 0 <= b < 1048576) by slia.
  assert (HSr : 2^20 <= SP <= 2^47) by (clear - RNG; lia).
  split; [rrs HSr RNG|]. split; [rrs HSr RNG|]. split; [rrs HSr RNG|]. split; [rrs HSr RNG|]. split; [rrs HSr RNG|]. split; [rrs HSr RNG|].
  split; [rrs HSr RNG|]. split; [rrs HSr RNG|]. split; [rrs HSr RNG|]. split; [rrs HSr RNG|]. split; [rrs HSr RNG|]. split; [rrs HSr RNG|]. split; [rrs HSr RNG|].
  split.
  - intros x Hx H1 H2 H3 H4. repeat (rewrite wb_other; [|clear - Hx; slia|clear - RNG; slia|lenb; clear - RNG; slia|lenb; clear - RNG Hx H1 H2 H3 H4; slia]). reflexivity.
  - growsc.
Qed.

(* [comment removed for export] *)
Lemma put_tail : forall {fx : FPState} rom m4 R8 D1 B1 n F st SP TR SZ h M4 hd b RA V0 V1 V2 V3 V4 V5 V6 V7 V8 V9,
  2^46 <= SP <= 2^47 -> SP mod 16 = 0 -> D1 + 1048576 <= SP - 2048 -> B1 + 8388608 <= SP - 2048 ->
  6529024 <= D1 -> 6529024 <= B1 -> (D1 + 1048576 <= B1 \/ B1 + 8388608 <= D1) -> D1 mod 16 = 0 ->
  0 <= n <= 65532 -> 0 <= st <= F -> F + 31 <= 1048000 -> SP <= TR -> TR + 8 * SZ <= 2^47 -> 1 <= SZ <= 30 ->
  0 <= h < 2^64 -> 0 <= M4 < 2^64 -> 0 <= hd < 2^31 -> 0 <= b < 1048576 ->
  0 <= RA < 2^64 -> 0 <= V0 < 2^64 -> 0 <= V1 < 2^64 -> 0 <= V2 < 2^64 -> 0 <= V3 < 2^64 -> 0 <= V4 < 2^64 ->
  0 <= V5 < 2^64 -> 0 <= V6 < 2^64 -> 0 <= V7 < 2^64 -> 0 <= V8 < 2^64 -> 0 <= V9 < 2^64 ->
  (forall i, 0 <= i < SZ -> exists w, 0 <= w < 2^64 /\ rd m4 (TR + 8 * i) 8 w) ->
  (forall x, B1 + 8 * F + 8 <= x < B1 + 8 * F + 8 + 8 * SZ -> store_ok SEGS m4 (wa x) 1 = true) ->
  (forall x, (SSS <= x < SSS + 4 \/ D1 + 16 * (n + 1) + 8 <= x < D1 + 16 * (n + 1) + 16 \/ TAB + 4 * b <= x < TAB + 4 * b + 4 \/
              SP - 136 <= x < SP - 128) -> wview SEGS m4 (wa x) <> None) ->
  rd m4 SSS 4 st ->
  rd m4 (SP - 208) 8 F -> rd m4 (SP - 152) 8 0x81ccc -> rd m4 (SP - 160) 8 (D1 + 16 * (n + 1)) -> rd m4 (SP - 168) 8 (D1 + 16 * (n + 1)) ->
  rd m4 (SP - 176) 8 (TAB + 4 * b) -> rd m4 (SP - 184) 8 h -> rd m4 (SP - 192) 8 M4 -> rd m4 (SP - 200) 8 hd ->
  rd m4 (SP - 120) 8 0x821b0 -> rd m4 (SP - 128) 8 0 -> rd m4 (SP - 136) 8 0 ->
  rd m4 (SP - 8) 8 RA -> rd m4 (SP - 16) 8 V0 -> rd m4 (SP - 24) 8 V1 -> rd m4 (SP - 32) 8 V2 -> rd m4 (SP - 40) 8 V3 ->
  rd m4 (SP - 48) 8 V4 -> rd m4 (SP - 56) 8 V5 -> rd m4 (SP - 64) 8 V6 -> rd m4 (SP - 72) 8 V7 -> rd m4 (SP - 80) 8 V8 -> rd m4 (SP - 88) 8 V9 ->
  getr R8 (Z_to_bv 5 (Z.of_nat 1)) = wa 0x7fa24 -> getr R8 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 208) ->
  getr R8 (Z_to_bv 5 (Z.of_nat 8)) = wa (SP - 136) -> getr R8 (Z_to_bv 5 (Z.of_nat 9)) = wa SSF ->
  getr R8 (Z_to_bv 5 (Z.of_nat 10)) = wa (B1 + 8 * F + 8) -> getr R8 (Z_to_bv 5 (Z.of_nat 11)) = wa TR ->
  getr R8 (Z_to_bv 5 (Z.of_nat 12)) = wa (8 * SZ) -> getr R8 (Z_to_bv 5 (Z.of_nat 18)) = wa (SZ + 1) ->
  getr R8 (Z_to_bv 5 (Z.of_nat 19)) = wa (SP - 104) -> getr R8 (Z_to_bv 5 (Z.of_nat 20)) = wa SZ ->
  getr R8 (Z_to_bv 5 (Z.of_nat 21)) = wa 0 -> getr R8 (Z_to_bv 5 (Z.of_nat 23)) = wa (n + 1) ->
  exists R11 m6, msteps SEGS (mkst R8 (wa 0x733c4) m4 rom) (mkst R11 (wa 0x821fc) m6 rom) /\
    getr R11 (Z_to_bv 5 (Z.of_nat 1)) = wa RA /\ getr R11 (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\
    getr R11 (Z_to_bv 5 (Z.of_nat 8)) = wa V0 /\ getr R11 (Z_to_bv 5 (Z.of_nat 9)) = wa V1 /\ getr R11 (Z_to_bv 5 (Z.of_nat 10)) = wa (n + 1) /\
    getr R11 (Z_to_bv 5 (Z.of_nat 18)) = wa V2 /\ getr R11 (Z_to_bv 5 (Z.of_nat 19)) = wa V3 /\ getr R11 (Z_to_bv 5 (Z.of_nat 20)) = wa V4 /\
    getr R11 (Z_to_bv 5 (Z.of_nat 21)) = wa V5 /\ getr R11 (Z_to_bv 5 (Z.of_nat 22)) = wa V6 /\ getr R11 (Z_to_bv 5 (Z.of_nat 23)) = wa V7 /\
    getr R11 (Z_to_bv 5 (Z.of_nat 24)) = wa V8 /\ getr R11 (Z_to_bv 5 (Z.of_nat 25)) = wa V9 /\
    (forall k, In k [3; 4; 26; 27]%nat -> getr R11 (Z_to_bv 5 (Z.of_nat k)) = getr R8 (Z_to_bv 5 (Z.of_nat k))) /\
    rd m6 SSS 4 (st + SZ + 1) /\ rd m6 (D1 + 16 * (n + 1) + 8) 4 hd /\ rd m6 (TAB + 4 * b) 4 (n + 1) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 136 <= x < SP - 128) -> ~ (SSS <= x < SSS + 4) -> ~ (D1 + 16 * (n + 1) + 8 <= x < D1 + 16 * (n + 1) + 16) ->
       ~ (TAB + 4 * b <= x < TAB + 4 * b + 4) -> ~ (B1 + 8 * F + 8 <= x < B1 + 8 * F + 8 + 8 * SZ) -> m6 (wa x) = m4 (wa x)) /\
    mem_grows m4 m6.
Proof.
  intros fx rom m4 R8 D1 B1 n F st SP TR SZ h M4 hd b RA V0 V1 V2 V3 V4 V5 V6 V7 V8 V9
    HSP HSPa HD1 HB1 D1a B1a S3 D1c Hn Hst HF HTR1 HTR2 HSZ Hh HM4 Hhd Hb HRA HV0 HV1 HV2 HV3 HV4 HV5 HV6 HV7 HV8 HV9
    HWORDS HBLK HWR RSS W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 W11 SV1 SV2 SV3 SV4 SV5 SV6 SV7 SV8 SV9 SV10 SV11
    R1 R2 R8' R9 R10 R11 R12 R18 R19 R20 R21 R23.
  assert (RNG : 2^46 <= SP <= 2^47 /\ D1 + 1048576 <= SP - 2048 /\ B1 + 8388608 <= SP - 2048 /\ 6529024 <= D1 /\ 6529024 <= B1 /\
                (D1 + 1048576 <= B1 \/ B1 + 8388608 <= D1) /\ 0 <= n <= 65532 /\ 0 <= st <= F /\ F + 31 <= 1048000 /\ 1 <= SZ <= 30 /\
                0 <= b < 1048576 /\ SP <= TR /\ TR + 8 * SZ <= 2^47) by slia.
  (* [comment removed for export] *)
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_mc0z.mc0_pmc0n R8 m4 rom 0 ltac:(constructor; [slia | rewrite R10, u_wa_small by slia; clear - RNG; slia | rewrite R12, u_wa_small by slia; clear - RNG; slia]))
    as (R9' & Hms9 & D12 & D13 & K9).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_mc0.RES_pmc0n fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot]. rewrite (zreg R8 _ 12 eq_refl), R12, u_wa_small by slia.
    apply Z.eqb_neq. rewrite !Z.mod_small by slia. slia. }
  change (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_mc0z.mc0_mem_pmc0n m4 R8 0) with m4 in Hms9. regz_all.
  rewrite R10, R12, !u_wa_small in D12 by slia. rewrite R10, u_wa_small in D13 by slia.
  (* [comment removed for export] *)
  assert (LM0 : LM (B1 + 8 * F + 8) TR (8 * SZ) R9' 0 R9').
  { split; [regzG; rewrite (K9 11%nat) by memb; rewrite R11; f_equal; slia|]. split; [regzG; rewrite D13; f_equal; slia|].
    split; [regzG; exact D12|]. intros k _. reflexivity. }
  destruct (memcpy_loop rom (B1 + 8 * F + 8) TR (8 * SZ) R9' ltac:(clear - RNG; slia) ltac:(clear - RNG; slia) ltac:(clear - RNG; slia)
              (Z.to_nat (8 * SZ)) 0 R9' m4 m4 ltac:(clear - RNG; slia) ltac:(clear - RNG; slia) LM0) as (R10' & m5 & Hms10 & K10 & FR5 & G5).
  { intros k Hk. assert (Hq : 0 <= k / 8 < SZ) by (split; [apply Z.div_pos; slia | apply Z.div_lt_upper_bound; slia]).
    destruct (HWORDS (k / 8) Hq) as (w & Hw & Rw).
    destruct (rd_byte m4 (TR + 8 * (k / 8)) 8 w (Z.to_nat (k mod 8)) ltac:(clear - RNG Hq; slia) ltac:(zn; clear - RNG Hq; slia) Rw
                ltac:(pose proof (Z.mod_pos_bound k 8 ltac:(slia)); slia)) as (bt & Hbt & Rbt).
    exists bt. split; [exact Hbt|]. rewrite Z2Nat.id in Rbt by (pose proof (Z.mod_pos_bound k 8 ltac:(slia)); slia).
    replace (TR + k) with (TR + 8 * (k / 8) + k mod 8) by (pose proof (Z.div_mod k 8 ltac:(slia)); slia). exact Rbt. }
  { intros k Hk. apply HBLK. clear - Hk. slia. }
  { intros x Hx H. reflexivity. }
  { apply mem_grows_refl. }
  (* [comment removed for export] *)
  assert (E10_2 : getr R10' (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 208)) by (rewrite (K10 2%nat), (K9 2%nat) by memb; exact R2).
  assert (FRB : forall a w v, rd m4 a w v -> 0 <= a -> a + Z.of_nat w <= 2^64 -> (a + Z.of_nat w <= B1 + 8 * F + 8 \/ B1 + 8 * F + 8 + 8 * SZ <= a) -> rd m5 a w v).
  { intros a w v R Ha Hw Hd. apply (rd_frame m4 m5); [exact Ha | exact Hw | | exact R]. intros x Hx. apply FR5; [clear - Ha Hw Hx; slia | clear - Hd Hx; slia]. }
  assert (WRB : forall a k, (forall x, a <= x < a + Z.of_nat k -> (SSS <= x < SSS + 4 \/ D1 + 16 * (n + 1) + 8 <= x < D1 + 16 * (n + 1) + 16 \/ TAB + 4 * b <= x < TAB + 4 * b + 4 \/ SP - 136 <= x < SP - 128)) ->
                0 <= a -> a + Z.of_nat k <= 2^64 -> store_ok SEGS m5 (wa a) k = true).
  { intros a k Hall Ha Hk. destruct k as [|k']; [reflexivity|]. rewrite Nat2Z.inj_succ in Hk.
    apply store_ok_of_all; [rewrite Nat2Z.inj_succ, u_wa_small by slia; slia|].
    intros x Hx. rewrite <- (wa_u x). rewrite Nat2Z.inj_succ, u_wa_small in Hx by slia.
    apply (wview_grows m4 m5 _ G5). apply HWR. apply Hall. slia. }
  assert (P11 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_ptlz.ptl_pre R10' m5 F st (D1 + 16 * (n + 1)) (TAB + 4 * b) h hd (n + 1) M4 RA V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 SZ TR).
  { constructor.
    1: (regzG; rewrite (K10 1%nat), (K9 1%nat) by memb; exact R1).
    1: (regzG; rewrite E10_2, (K10 8%nat), (K9 8%nat) by memb; rewrite R8', u_wa_small by slia; f_equal; slia).
    1: (regzG; rewrite (K10 9%nat), (K9 9%nat) by memb; exact R9).
    1: (regzG; rewrite (K10 18%nat), (K9 18%nat) by memb; exact R18).
    1: (regzG; rewrite E10_2, (K10 19%nat), (K9 19%nat) by memb; rewrite R19, u_wa_small by slia; f_equal; slia).
    1: (regzG; rewrite (K10 20%nat), (K9 20%nat) by memb; exact R20).
    1: (regzG; rewrite (K10 21%nat), (K9 21%nat) by memb; exact R21).
    1: (regzG; rewrite (K10 23%nat), (K9 23%nat) by memb; exact R23).
    all: rewrite ?E10_2, ?u_wa_small by (clear - RNG; slia).
    1-22: (clear - RNG HRA HV0 HV1 HV2 HV3 HV4 HV5 HV6 HV7 HV8 HV9 Hh HM4 Hhd; slia).
    1: (rewrite Zminus_mod, HSPa; reflexivity).
    - replace (SP - 208 + 0) with (SP - 208) by slia. apply FRB; [exact W1 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 56) with (SP - 152) by slia. apply FRB; [exact W2 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 48) with (SP - 160) by slia. apply FRB; [exact W3 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 40) with (SP - 168) by slia. apply FRB; [exact W4 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 32) with (SP - 176) by slia. apply FRB; [exact W5 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 24) with (SP - 184) by slia. apply FRB; [exact W6 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 16) with (SP - 192) by slia. apply FRB; [exact W7 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 8) with (SP - 200) by slia. apply FRB; [exact W8 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 88) with (SP - 120) by slia. apply FRB; [exact W9 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 80) with (SP - 128) by slia. apply FRB; [exact W10 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 72) with (SP - 136) by slia. apply FRB; [exact W11 | slia | zn; slia | zn; clear - RNG; slia].
    - intros d k Hd Hk. apply WRB; [| clear - RNG Hd; slia | clear - RNG Hd Hk; slia]. intros x Hx. clear - Hx Hd Hk. slia.
    - replace (SP - 208 + 200) with (SP - 8) by slia. apply FRB; [exact SV1 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 192) with (SP - 16) by slia. apply FRB; [exact SV2 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 184) with (SP - 24) by slia. apply FRB; [exact SV3 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 176) with (SP - 32) by slia. apply FRB; [exact SV4 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 168) with (SP - 40) by slia. apply FRB; [exact SV5 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 160) with (SP - 48) by slia. apply FRB; [exact SV6 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 152) with (SP - 56) by slia. apply FRB; [exact SV7 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 144) with (SP - 64) by slia. apply FRB; [exact SV8 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 136) with (SP - 72) by slia. apply FRB; [exact SV9 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 128) with (SP - 80) by slia. apply FRB; [exact SV10 | slia | zn; slia | zn; clear - RNG; slia].
    - replace (SP - 208 + 120) with (SP - 88) by slia. apply FRB; [exact SV11 | slia | zn; slia | zn; clear - RNG; slia].
    - rewrite (Z.mod_small (Z.shiftr F 16)) by (rewrite Z.shiftr_div_pow2 by slia; split; [apply Z.div_pos; slia | apply Z.div_lt_upper_bound; slia]).
      rewrite Z.shiftr_shiftr by slia. rewrite (shiftr_small F (16 + 4)) by (clear - RNG; slia). slia.
    - change (0 + 1797280) with SSS. apply FRB; [exact RSS | slia | zn; slia | zn; clear - RNG; slia].
    - intros d k Hd Hk. apply WRB; [| clear - Hd; slia | clear - Hd Hk; slia]. intros x Hx. clear - Hx Hd Hk. slia.
    - rewrite Z.add_mod, D1c by slia. rewrite Z.mul_comm, Z.mod_mul by slia. reflexivity.
    - intros d k Hd Hk. apply WRB; [| clear - RNG Hd; slia | clear - RNG Hd Hk; slia]. intros x Hx. clear - Hx Hd Hk. slia.
    - rewrite Z.add_mod by slia. rewrite Z.mul_comm, Z.mod_mul by slia. reflexivity.
    - intros d k Hd Hk. apply WRB; [| clear - RNG Hd; slia | clear - RNG Hd Hk; slia]. intros x Hx. clear - Hx Hd Hk RNG. slia.
    - clear - RNG; slia.
    - clear - RNG; slia.
    - clear - RNG; slia.
    - clear - RNG; slia.
    - clear - RNG; slia.
    - clear - RNG; slia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_ptlz.ptl_pptl R10' m5 rom F st (D1 + 16 * (n + 1)) (TAB + 4 * b) h hd (n + 1) M4 RA V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 SZ TR P11)
    as (R11' & Hms11 & E1 & E2 & E8 & E9 & E10 & E12 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & K11).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_ptl.RES_pptl fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    cbn [sc_denot]. rewrite (pack_zero _ (EVar 51) (EVar 33) SZ st).
    - reflexivity.
    - slia.
    - slia.
    - clear - RNG; slia.
    - apply (zatom R10' (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_ptlz.VALS_ptl F st (D1 + 16 * (n + 1)) (TAB + 4 * b) h hd (n + 1) M4 RA V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 SZ TR) 51 SZ eq_refl eq_refl). slia.
    - apply (zatom R10' (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_ptlz.VALS_ptl F st (D1 + 16 * (n + 1)) (TAB + 4 * b) h hd (n + 1) M4 RA V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 SZ TR) 33 st eq_refl eq_refl). slia. }
  regz_all. rewrite E10_2, u_wa_small in E2 by slia.
  set (m6 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_ptlz.ptl_mem_pptl m5 R10' F st (D1 + 16 * (n + 1)) (TAB + 4 * b) h hd (n + 1) M4 RA V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 SZ TR).
  assert (Em6 : m6 = wbytes (wbytes (wbytes (wbytes (wbytes m5 (wa SSS) (word_to_le_bytes 4 (wa (st + SZ + 1))))
               (wa (SP - 136)) (word_to_le_bytes 8 (wa 0))) (wa (D1 + 16 * (n + 1) + 12)) (word_to_le_bytes 4 (wa (F + 1))))
               (wa (D1 + 16 * (n + 1) + 8)) (word_to_le_bytes 4 (wa hd))) (wa (TAB + 4 * b)) (word_to_le_bytes 4 (wa (n + 1)))).
  { unfold m6, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_ptlz.ptl_mem_pptl. regz_all. rewrite E10_2, u_wa_small by (clear - RNG; slia).
    repeat (apply (f_equal3 wbytes)); try reflexivity; first [apply f_equal; clear - RNG; slia | apply f_equal; apply f_equal; clear - RNG; slia]. }
  exists R11', m6. split; [exact (msteps_trans SEGS _ _ _ Hms9 (msteps_trans SEGS _ _ _ Hms10 Hms11))|].
  split; [exact E1|]. split; [rewrite E2; f_equal; slia|]. split; [exact E8|]. split; [exact E9|]. split; [exact E10|].
  split; [exact E18|]. split; [exact E19|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|]. split; [exact E23|].
  split; [exact E24|]. split; [exact E25|].
  split; [intros k Hk; rewrite (K11 k) by (clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]); rewrite (K10 k) by (clear - Hk; unfold KM; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]);
          exact (K9 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in *; tauto ]))|].
  rewrite Em6. clear Em6 m6.
  split; [rr RNG|]. split; [rr RNG|]. split; [rr RNG|].
  split.
  - intros x Hx H1 H2 H3 H4 H5. repeat (rewrite wb_other; [|clear - Hx; slia|clear - RNG; slia|lenb; clear - RNG; slia|lenb; clear - RNG Hx H1 H2 H3 H4; slia]).
    apply FR5; [exact Hx | clear - H5; slia].
  - repeat apply grows_wb. exact G5.
Qed.
End AXG_put4.

Module AXG_put5.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import RefMemcpyLib SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AxAsan AXG_put AXG_put2 AXG_put3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AxAsan OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AXG_put4.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac is_arith T := lazymatch T with
  | @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq nat _ _ => idtac | Nat.le _ _ => idtac | Nat.lt _ _ => idtac | le _ _ => idtac | lt _ _ => idtac
  | ?A /\ ?B => is_arith A; is_arith B
  | ?A \/ ?B => is_arith A; is_arith B
  | ~ ?A => is_arith A
  | True => idtac | False => idtac
  end.
Ltac prune_ctx := repeat match goal with
  | H : ?T |- _ => lazymatch type of T with
                   | Prop => tryif is_arith T then fail else clear H
                   | _ => fail
                   end
  end.
Ltac prune_mod := lazymatch goal with
  | |- context [Z.modulo _ _] => idtac
  | |- context [Z.div _ _] => idtac
  | _ => repeat match goal with
              | H : Z.modulo _ _ = _ |- _ => clear H
              | H : context [Z.modulo _ _] |- _ => lazymatch type of H with _ /\ _ => let H1 := fresh "C" in let H2 := fresh "C" in pose proof H as [H1 H2]; clear H end
              end
  end.
Ltac slia := first [ LiaFast.lia_fast_tiers | (prune_ctx; prune_mod; lia) ].
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Lemma m1_saves : forall m regs SP, getr regs 2 = wa SP -> 2^46 <= SP <= 2^47 ->
  let m1 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt0z.pt0_mem_ppt0 m regs 0 in
  rd m1 (SP - 8) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) /\ rd m1 (SP - 16) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))) /\
  rd m1 (SP - 24) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) /\ rd m1 (SP - 32) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) /\
  rd m1 (SP - 40) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))) /\ rd m1 (SP - 48) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) /\
  rd m1 (SP - 56) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) /\ rd m1 (SP - 64) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22)))) /\
  rd m1 (SP - 72) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) /\ rd m1 (SP - 80) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) /\
  rd m1 (SP - 88) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25)))) /\ rd m1 (SP - 104) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 10)))) /\
  rd m1 (SP - 96) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 11)))) /\ mem_grows m m1.
Proof.
  intros m regs SP HSP Hr m1. unfold m1, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt0z.pt0_mem_ppt0. regz_all. rewrite HSP, u_wa_small by slia.
  set (v := fun k => bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat k)))).
  assert (HR : 2^46 <= SP <= 2^47) by exact Hr. clear HSP Hr.
  Ltac rr1 H := repeat first [ (apply wb_rd_hit; [slia | clear - H; slia | zn; clear - H; slia])
                             | (apply wb_rd_other; [clear - H; slia | zn; clear - H; slia | clear - H; slia | lenb; clear - H; slia | lenb; clear - H; slia | ]) ].
  repeat (replace (SP + -8) with (SP - 8) by slia); repeat (replace (SP + -16) with (SP - 16) by slia);
  repeat (replace (SP + -24) with (SP - 24) by slia); repeat (replace (SP + -32) with (SP - 32) by slia);
  repeat (replace (SP + -40) with (SP - 40) by slia); repeat (replace (SP + -48) with (SP - 48) by slia);
  repeat (replace (SP + -56) with (SP - 56) by slia); repeat (replace (SP + -64) with (SP - 64) by slia);
  repeat (replace (SP + -72) with (SP - 72) by slia); repeat (replace (SP + -80) with (SP - 80) by slia);
  repeat (replace (SP + -88) with (SP - 88) by slia); repeat (replace (SP + -104) with (SP - 104) by slia);
  repeat (replace (SP + -96) with (SP - 96) by slia).
  assert (HSr : 2^20 <= SP <= 2^47) by (clear - HR; lia).
  do 13 (split; [rrs HSr HR; apply bv_unsigned_in_range|]). growsc.
Qed.

(* [comment removed for export] *)
Theorem put_contract : forall {fx : FPState} rom m regs D1 B1 n F st TR SZ SP,
  INV_D m D1 B1 n F st -> n <= 65532 -> F + 31 <= 1048000 ->
  getr regs 2 = wa SP -> 2^46 <= SP <= 2^47 -> SP mod 16 = 0 -> stk_ok SEGS m (wa SP) 2048 ->
  D1 + 1048576 <= SP - 2048 -> B1 + 8388608 <= SP - 2048 ->
  getr regs 10 = wa TR -> getr regs 11 = wa SZ -> SP <= TR -> TR + 8 * SZ <= 2^47 -> 1 <= SZ <= 30 ->
  (forall i, 0 <= i < SZ -> exists w, 0 <= w < 2^64 /\ rd m (TR + 8 * i) 8 w) ->
  (forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None) ->
  exists R m' n' F' st', msteps SEGS (mkst regs (wa 0x81f88) m rom) (mkst R (wa 0x821fc) m' rom) /\
    getr R (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\
    (forall k, In k [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    INV_D m' D1 B1 n' F' st' /\ n <= n' <= n + 1 /\ F <= F' <= F + SZ + 1 /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ downed D1 B1 x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof.
  intros fx rom m regs D1 B1 n F st TR SZ SP I Hn HF HSP HSPr HSPa HSTK HD1 HB1 HR10 HR11 HTR1 HTR2 HSZ HWORDS HIMG.
  pose proof I as I0. destruct I0 as [Inu Inr Imap ID1 Itab IF Ist IFr IB1 IB1r Iwr Isep In0].
  assert (HBKT : forall b, 0 <= b < 1048576 -> exists hd, 0 <= hd < 2^31 /\ rd m (TAB + 4 * b) 4 hd).
  { intros b Hb. destruct (Itab b Hb) as (hd & H1 & H2 & _). exists hd. split; assumption. }
  destruct (put_phaseA rom m regs TR SZ SP HSP ltac:(slia) HSTK HR10 HR11 ltac:(slia) ltac:(slia) HWORDS HIMG HBKT)
    as (RA' & h & hd & HmsA & Hh & Hhd & Rhd & A11 & A22 & A23 & A24 & A19 & A18 & A25 & A9 & A8 & A2 & KA).
  set (m1 := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt0z.pt0_mem_ppt0 m regs 0) in *.
  destruct (m1_saves m regs SP HSP HSPr) as (SV1 & SV2 & SV3 & SV4 & SV5 & SV6 & SV7 & SV8 & SV9 & SV10 & SV11 & SV12 & SV13 & G1).
  fold m1 in SV1, SV2, SV3, SV4, SV5, SV6, SV7, SV8, SV9, SV10, SV11, SV12, SV13, G1.
  assert (HM1 : forall x, 0 <= x < 2^64 -> ~ (SP - 112 <= x < SP) -> m1 (wa x) = m (wa x)).
  { intros x Hx H. apply (m1_out m regs TR SZ SP HSP ltac:(slia) HR10 HR11); [exact Hx | slia]. }
  assert (FRM : forall a w v, rd m a w v -> 0 <= a -> a + Z.of_nat w <= 2^64 -> (a + Z.of_nat w <= SP - 112 \/ SP <= a) -> rd m1 a w v).
  { intros a w v R Ha Hw Hd. apply (rd_frame m m1); [exact Ha | exact Hw | | exact R]. intros x Hx. apply HM1; [clear - Ha Hw Hx; slia | clear - Hd Hx; slia]. }
  unfold AXG_put2.m1 in HmsA. fold m1 in HmsA.
  clearbody m1.
  destruct ID1 as (D1a & D1b & D1c). destruct Isep as (S1 & S2 & S3).
  (* [comment removed for export] *)
  destruct (Itab (h mod 2^20) ltac:(pose proof (Z.mod_pos_bound h (2^20) ltac:(slia)); slia)) as (hd0 & Hhd0 & Rhd0 & k0 & Hc0).
  assert (Ehd : hd0 = hd) by (apply (rd_inj m (TAB + 4 * (h mod 2^20)) 4 hd0 hd); [slia | zn; slia | zn; slia | exact Rhd0 | exact Rhd]). subst hd0.
  assert (Hc1 : chainz m1 D1 n k0 hd).
  { apply (chainz_frame m m1 D1 n k0 hd); [slia | slia | slia | | exact Hc0]. intros x Hx. apply HM1; [slia | slia]. }
  assert (HN0 : exists hv lk, 0 <= hv < 2^64 /\ 0 <= lk < 2^32 /\ rd m1 D1 8 hv /\ rd m1 (D1 + 8) 4 lk).
  { destruct In0 as (hv & lk & H1 & H2 & R1 & R2). exists hv, lk. split; [exact H1|]. split; [exact H2|].
    split; [apply FRM; [exact R1 | slia | zn; slia | zn; slia] | apply FRM; [exact R2 | slia | zn; slia | zn; slia]]. }
  assert (LF0 : LF RA' hd RA').
  { split; [regzG; exact A11|]. split; [regzG; exact A22|]. split; [regzG; exact A23|]. intros j _. reflexivity. }
  destruct (find_loop rom m1 D1 n h RA' ltac:(slia) ltac:(slia) ltac:(apply FRM; [exact Imap | slia | zn; slia | zn; slia]) HN0 Hh A24 A19 k0 hd RA' Hc1 LF0)
    as [(RF & HmsF & LFF)|(RF & id' & Hid' & HmsF & F10 & KF')].
  2: { (* [comment removed for export] *)
    assert (EF2 : getr RF (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 112)) by (rewrite (KF' 2%nat) by memb; exact A2).
    assert (P5 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pez.pe_pre RF m1 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))
                   (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))
                   (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))
                   (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24)))) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))).
    { constructor.
      1-11: (match goal with |- 0 <= bv_unsigned ?w <= _ => pose proof (bv_unsigned_in_range _ w) as X; unfold bv_modulus in X; change (2 ^ Z.of_N 64) with (2^64) in X; clear - X; lia end).
      all: rewrite EF2, u_wa_small by slia.
      1: slia.
      1: (rewrite Zminus_mod, HSPa; reflexivity).
      1: (replace (SP - 112 + 104) with (SP - 8) by slia; exact SV1).
      1: (replace (SP - 112 + 96) with (SP - 16) by slia; exact SV2).
      1: (replace (SP - 112 + 88) with (SP - 24) by slia; exact SV3).
      1: (replace (SP - 112 + 80) with (SP - 32) by slia; exact SV4).
      1: (replace (SP - 112 + 72) with (SP - 40) by slia; exact SV5).
      1: (replace (SP - 112 + 64) with (SP - 48) by slia; exact SV6).
      1: (replace (SP - 112 + 56) with (SP - 56) by slia; exact SV7).
      1: (replace (SP - 112 + 48) with (SP - 64) by slia; exact SV8).
      1: (replace (SP - 112 + 40) with (SP - 72) by slia; exact SV9).
      1: (replace (SP - 112 + 32) with (SP - 80) by slia; exact SV10).
      1: (replace (SP - 112 + 24) with (SP - 88) by slia; exact SV11). }
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pez.pe_ppe RF m1 rom _ _ _ _ _ _ _ _ _ _ _ P5 ltac:(constructor)) as (RE & HmsE & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & KE).
    change (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pez.pe_mem_ppe m1 RF _ _ _ _ _ _ _ _ _ _ _) with m1 in HmsE. regz_all.
    exists RE, m1, n, F, st. split; [exact (msteps_trans SEGS _ _ _ HmsA (msteps_trans SEGS _ _ _ HmsF HmsE))|].
    split; [rewrite E2, EF2, u_wa_small by slia; f_equal; slia|].
    split.
    - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
      all: first [ (rewrite E1; apply wa_u) | (rewrite E8; apply wa_u) | (rewrite E9; apply wa_u) | (rewrite E18; apply wa_u)
             | (rewrite E19; apply wa_u) | (rewrite E20; apply wa_u) | (rewrite E21; apply wa_u) | (rewrite E22; apply wa_u) | (rewrite E23; apply wa_u)
             | (rewrite E24; apply wa_u) | (rewrite E25; apply wa_u)
             | (match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ => rewrite (KE k) by memb; rewrite (KF' k) by memb; exact (KA k ltac:(memb)) end) ].
    - split; [apply (INV_D_frame m m1); [exact I | intros x Hx Hd; apply HM1; [exact Hx | unfold downed in Hd; slia]]|].
      split; [slia|]. split; [slia|]. split; [intros x Hx H1 H2; apply HM1; [exact Hx | slia] | exact G1]. }
  (* [comment removed for export] *)
  destruct LFF as (F11 & F22 & F23 & KFF).
  set (b := h mod 2^20) in *.
  assert (Hb : 0 <= b < 1048576) by (unfold b; pose proof (Z.mod_pos_bound h (2^20) ltac:(slia)); slia).
  clearbody b.
  assert (RNG : 2^46 <= SP <= 2^47 /\ D1 + 1048576 <= SP - 2048 /\ B1 + 8388608 <= SP - 2048 /\ 6529024 <= D1 /\ 6529024 <= B1 /\
                (D1 + 1048576 <= B1 \/ B1 + 8388608 <= D1) /\ 0 <= n <= 65532 /\ 0 <= st <= F /\ F + 31 <= 1048000 /\ 1 <= SZ <= 30 /\
                0 <= b < 1048576 /\ SP <= TR /\ TR + 8 * SZ <= 2^47) by slia.
  pose proof S3 as S3'. clear HSPr HD1 HB1 HTR1 HTR2 HSZ Hn HF D1a D1b S1 S2 S3 Inr IFr.
  assert (EF2 : getr RF (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 112)) by (rewrite (KFF 2%nat) by memb; exact A2).
  destruct (put_lock rom m m1 RF SP b hd D1 B1 n F st I ltac:(slia) HSPa HSTK G1 HM1 Hb Hhd ltac:(exact Rhd) EF2
              ltac:(rewrite (KFF 18%nat) by memb; exact A18) ltac:(rewrite (KFF 25%nat) by memb; exact A25))
    as (R6 & m2 & Hms6 & B21 & K6 & M2 & G2).
  assert (G12 : mem_grows m m2) by (intros x Hx; apply G2, G1, Hx).
  assert (M12 : forall x, 0 <= x < 2^64 -> x < SP - 2048 -> ~ (TAB + 4 * b <= x < TAB + 4 * b + 4) -> m2 (wa x) = m (wa x)).
  { intros x Hx H1 H2. rewrite M2 by (first [exact Hx | slia | exact H2]). apply HM1; [exact Hx | slia]. }
  destruct (put_id rom m m2 R6 D1 B1 n F st I ltac:(slia) G12
              ltac:(apply (rd_frame m m2); [slia | zn; slia | intros x Hx; zn; apply M12; slia | exact Inu])
              ltac:(rewrite (K6 9%nat), (KFF 9%nat) by memb; exact A9))
    as (R7 & Hms7 & C9 & C10 & K7).
  set (m3 := wbytes m2 (wa NUNIQ) (word_to_le_bytes 4 (wa (n + 1)))) in *.
  assert (M3 : forall x, 0 <= x < 2^64 -> ~ (NUNIQ <= x < NUNIQ + 4) -> m3 (wa x) = m2 (wa x)).
  { intros x Hx H. unfold m3. rewrite wb_other; [reflexivity | exact Hx | slia | lenb; slia | lenb; slia]. }
  assert (G13 : mem_grows m m3) by (intros x Hx; apply wbytes_grows, G12, Hx).
  assert (RN3 : rd m3 NUNIQ 4 (n + 1)) by (unfold m3; apply wb_rd_hit; [slia | slia | zn; slia]).
  clearbody m3.
  assert (FR3 : forall x, 0 <= x < 2^64 -> downed D1 B1 x -> ~ (NUNIQ <= x < NUNIQ + 4) -> ~ (TAB + 4 * b <= x < TAB + 4 * b + 4) -> m3 (wa x) = m (wa x)).
  { intros x Hx Hd H1 H2. rewrite M3 by assumption. apply M12; [exact Hx | unfold downed in Hd; slia | exact H2]. }
  assert (FS3 : forall a w v, rd m1 a w v -> SP - 112 <= a -> a + Z.of_nat w <= SP -> rd m3 a w v).
  { intros a w v R H1 H2. apply (rd_frame m1 m3); [slia | slia | | exact R]. intros x Hx. rewrite M3 by slia. apply M2; slia. }
  destruct (put_node rom m m3 R7 D1 B1 n F st SP TR SZ h (bv_unsigned (getr R7 (Z_to_bv 5 (Z.of_nat 20)))) hd b I ltac:(slia) ltac:(slia) ltac:(slia) HSPa HSTK
              ltac:(slia) ltac:(slia) ltac:(slia) ltac:(slia) Hh ltac:(apply bv_unsigned_in_range) ltac:(slia) Hb G13 FR3
              ltac:(apply FS3; [regzH HR10; rewrite HR10, u_wa_small in SV12 by slia; exact SV12 | slia | zn; slia]) ltac:(apply FS3; [regzH HR11; rewrite HR11, u_wa_small in SV13 by slia; exact SV13 | slia | zn; slia])
              ltac:(rewrite (K7 2%nat), (K6 2%nat) by memb; exact EF2) ltac:(rewrite (K7 8%nat), (K6 8%nat), (KFF 8%nat) by memb; exact A8)
              C9 C10 ltac:(rewrite (K7 22%nat), (K6 22%nat) by memb; exact F22) ltac:(rewrite (K7 23%nat), (K6 23%nat) by memb; exact F23)
              ltac:(rewrite (K7 24%nat), (K6 24%nat), (KFF 24%nat) by memb; exact A24) ltac:(rewrite (K7 18%nat), (K6 18%nat), (KFF 18%nat) by memb; exact A18)
              ltac:(rewrite (K7 19%nat), (K6 19%nat), (KFF 19%nat) by memb; exact A19) ltac:(rewrite wa_u; reflexivity)
              ltac:(rewrite (K7 21%nat) by memb; exact B21))
    as (R8 & m4 & Hms8 & D1' & D2 & D8 & D9 & D10 & D11 & D12 & D18 & D19 & D20 & D21 & D23 & K8 &
        W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & RH4 & RF4 & M4r & G4).
  (* [comment removed for export] *)
  assert (FA4 : forall x, 0 <= x < 2^64 -> SP <= x -> m4 (wa x) = m (wa x)).
  { intros x Hx H. rewrite M4r by (first [exact Hx | slia]). rewrite M3 by slia. rewrite M2 by slia. apply HM1; [exact Hx | slia]. }
  assert (FO4 : forall x, 0 <= x < 2^64 -> downed D1 B1 x -> ~ (NUNIQ <= x < NUNIQ + 4) -> ~ (TAB + 4 * b <= x < TAB + 4 * b + 4) ->
                ~ (D1 + 16 * (n + 1) <= x < D1 + 16 * (n + 1) + 8) -> ~ (SSF <= x < SSF + 8) -> ~ (B1 + 8 * F <= x < B1 + 8 * F + 8) -> m4 (wa x) = m (wa x)).
  { intros x Hx Hd H1 H2 H3 H4 H5. rewrite M4r by (first [exact Hx | exact H3 | exact H4 | exact H5 | (unfold downed in Hd; slia)]). exact (FR3 x Hx Hd H1 H2). }
  assert (FS4 : forall a w v, rd m1 a w v -> SP - 112 <= a -> a + Z.of_nat w <= SP -> rd m4 a w v).
  { intros a w v R H1 H2. apply (rd_frame m3 m4); [slia | slia | | exact (FS3 a w v R H1 H2)]. intros x Hx. apply M4r; slia. }
  assert (G14 : mem_grows m m4) by (intros x Hx; apply G4, G13, Hx).
  assert (WRO : forall x, downed D1 B1 x -> wview SEGS m4 (wa x) <> None) by (intros x Hx; apply (wview_grows m m4 x G14); exact (Iwr x Hx)).
  set (vv := fun k => bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat k)))).
  assert (Hvv : forall k, 0 <= vv k < 2^64) by (intros k; apply bv_unsigned_in_range).
  assert (Evv : forall k, wa (vv k) = getr regs (Z_to_bv 5 (Z.of_nat k))) by (intros k; apply wa_u).
  destruct (put_tail rom m4 R8 D1 B1 n F st SP TR SZ h (bv_unsigned (getr R7 (Z_to_bv 5 (Z.of_nat 20)))) hd b
              (vv 1%nat) (vv 8%nat) (vv 9%nat) (vv 18%nat) (vv 19%nat) (vv 20%nat) (vv 21%nat) (vv 22%nat) (vv 23%nat) (vv 24%nat) (vv 25%nat)
              ltac:(slia) HSPa ltac:(slia) ltac:(slia) ltac:(slia) ltac:(slia) S3' D1c ltac:(slia) ltac:(slia) ltac:(slia) ltac:(slia) ltac:(slia) ltac:(slia)
              Hh ltac:(apply bv_unsigned_in_range) ltac:(slia) Hb (Hvv 1%nat) (Hvv 8%nat) (Hvv 9%nat) (Hvv 18%nat) (Hvv 19%nat) (Hvv 20%nat) (Hvv 21%nat)
              (Hvv 22%nat) (Hvv 23%nat) (Hvv 24%nat) (Hvv 25%nat))
    as (R11 & m6 & Hms11 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & KT & RSS6 & RL6 & RB6 & M6r & G6).
  { intros j Hj. destruct (HWORDS j Hj) as (w & Hw & Rw). exists w. split; [exact Hw|].
    apply (rd_frame m m4); [slia | zn; slia | | exact Rw]. intros x Hx. zn. apply FA4; slia. }
  { intros x Hx. apply (wr_owned m m4 D1 B1 n F st _ 1 I G14); [slia | zn; slia | intros y Hy; zn; unfold downed; slia]. }
  { intros x Hx. destruct Hx as [Hx|[Hx|[Hx|Hx]]]; [apply WRO; unfold downed; slia | apply WRO; unfold downed; slia | apply WRO; unfold downed; slia |].
    assert (Hs : store_ok SEGS m (wa x) 1 = true) by (apply HSTK; rewrite !u_wa_small by slia; zn; slia).
    apply (wview_grows m m4 x G14). apply (store_ok_all SEGS m 1 (wa x)); [rewrite u_wa_small by slia; zn; slia | exact Hs | rewrite u_wa_small by slia; zn; slia]. }
  { apply (rd_frame m m4); [slia | zn; slia | | exact Ist]. intros x Hx. zn. apply FO4; [slia | unfold downed; slia | slia | slia | slia | slia | slia]. }
  all: try exact W1. all: try exact W2. all: try exact W3. all: try exact W4. all: try exact W5. all: try exact W6.
  all: try exact W7. all: try exact W8. all: try exact W9. all: try exact W10. all: try exact W11.
  all: try (apply FS4; [first [exact SV1 | exact SV2 | exact SV3 | exact SV4 | exact SV5 | exact SV6 | exact SV7 | exact SV8 | exact SV9 | exact SV10 | exact SV11] | clear; lia | zn; clear; lia]).
  all: try assumption.
  clearbody vv.
  assert (G16 : mem_grows m m6) by (intros x Hx; apply G6, G14, Hx).
  assert (F64 : forall x, 0 <= x < 2^64 -> ~ (SP - 136 <= x < SP - 128) -> ~ (SSS <= x < SSS + 4) -> ~ (D1 + 16 * (n + 1) + 8 <= x < D1 + 16 * (n + 1) + 16) ->
                ~ (TAB + 4 * b <= x < TAB + 4 * b + 4) -> ~ (B1 + 8 * F + 8 <= x < B1 + 8 * F + 8 + 8 * SZ) -> m6 (wa x) = m4 (wa x)) by exact M6r.
  assert (INV' : INV_D m6 D1 B1 (n + 1) (F + SZ + 1) (st + SZ + 1)).
  { apply (INV_D_insert m m6 D1 B1 n F st b hd h SZ I ltac:(slia) ltac:(slia) ltac:(slia) Hb Hh Rhd ltac:(slia)).
    - apply (rd_frame m3 m6); [slia | zn; slia | | exact RN3].
      intros x Hx. zn. rewrite F64 by slia. apply M4r; slia.
    - exact RB6.
    - apply (rd_frame m4 m6); [slia | zn; slia | | exact RH4]. intros x Hx. zn. apply F64; slia.
    - exact RL6.
    - apply (rd_frame m4 m6); [slia | zn; slia | | exact RF4]. intros x Hx. zn. apply F64; slia.
    - exact RSS6.
    - intros x Hx Hd H1 H2 H3 H4 H5 H6. rewrite F64 by (first [exact Hx | exact H5 | (unfold downed in Hd; slia) | slia]).
      apply FO4; [exact Hx | exact Hd | exact H1 | exact H2 | slia | exact H4 | slia].
    - exact G16. }
  exists R11, m6, (n + 1), (F + SZ + 1), (st + SZ + 1).
  split; [exact (msteps_trans SEGS _ _ _ HmsA (msteps_trans SEGS _ _ _ HmsF (msteps_trans SEGS _ _ _ Hms6 (msteps_trans SEGS _ _ _ Hms7
          (msteps_trans SEGS _ _ _ Hms8 Hms11)))))|].
  split; [exact E2|].
  split.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
    all: first [ (rewrite E1; apply Evv) | (rewrite E8; apply Evv) | (rewrite E9; apply Evv) | (rewrite E18; apply Evv)
             | (rewrite E19; apply Evv) | (rewrite E20; apply Evv) | (rewrite E21; apply Evv) | (rewrite E22; apply Evv) | (rewrite E23; apply Evv)
             | (rewrite E24; apply Evv) | (rewrite E25; apply Evv)
             | (match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
                  rewrite (KT k) by memb; rewrite (K8 k) by memb; rewrite (K7 k) by memb; rewrite (K6 k) by memb; rewrite (KFF k) by memb; exact (KA k ltac:(memb)) end) ].
  - split; [exact INV'|]. split; [slia|]. split; [slia|]. split; [|exact G16].
    intros x Hx H1 H2. rewrite F64 by (first [exact Hx | (unfold downed in H2; slia)]). rewrite M4r by (first [exact Hx | (unfold downed in H2; slia)]).
    rewrite M3 by (first [exact Hx | (unfold downed in H2; slia)]). rewrite M2 by (first [exact Hx | (unfold downed in H2; slia)]). apply HM1; [exact Hx | slia].
Qed.
End AXG_put5.

Module AcPutApp.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AXG_put5.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg AcDenW AcHand.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma isteps_of_msteps : forall segs ms ms', CatSim.msteps segs ms ms' -> isteps segs ms ms'.
Proof. intros segs ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hst _ IH]; [apply ist_refl | eapply ist_step; eassumption]. Qed.

(* [comment removed for export] *)
Lemma restrict_mkst : forall H ms, ms_svc_pending ms = None -> ms_resv ms = None ->
  restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (ms_pc_val ms) (mrestrict H (ms_mem ms)) (ms_rom ms).
Proof. intros H [r f p s rv c m ro] Hs Hr. cbn in Hs, Hr. subst. reflexivity. Qed.

Definition rk (r : Z) : positive := bv_key (Z_to_bv 5 r).
Definition KALLk : list positive := List.map rk [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27].

Section PutApp.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap SEGS.

#[using="Type"] Lemma getr_lit : forall regs k, getr regs (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)). Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mrg_reg : forall E n L S ms r l, sden0 SEGS E (mrg (sst_shift n L) S) ms -> rget (s_regs L) (rkey r) = l ->
  getr (ms_regs ms) r = lden (vshift n E) l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E n L S ms r l Hd Hl. destruct Hd as (_ & _ & _ & HR & _). rewrite (HR r). cbn [mrg sst_shift s_regs].
  rewrite rget_shift, lden_shift, Hl. reflexivity.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma mrg_rg : forall E n L S ms i R, sden0 SEGS E (mrg (sst_shift n L) S) ms -> nth_error (s_rgs L) i = Some R ->
  rg_ok SEGS (vshift n E) (ms_mem ms) R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E n L S ms i R Hd Hi. destruct Hd as (_ & _ & _ & _ & HG & _). cbn [mrg sst_shift s_rgs] in HG.
  apply Forall_app in HG as [HG _]. rewrite Forall_map, Forall_forall in HG. apply rg_ok_shift. exact (HG R (nth_error_In _ _ Hi)).
Qed.
#[using="Type"] Lemma mrg_fact : forall E n L S ms f, sden0 SEGS E (mrg (sst_shift n L) S) ms -> In f (s_facts L) -> fact_ok (vshift n E) f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E n L S ms f Hd Hf. destruct Hd as (_ & _ & _ & _ & _ & _ & HF & _). cbn [mrg sst_shift s_facts] in HF.
  apply Forall_app in HF as [HF _]. rewrite Forall_map, Forall_forall in HF. apply fact_ok_shift. exact (HF f Hf).
Qed.

#[using="Type"] Lemma rdn_some : forall m (a : Z) n, 0 <= a -> a + Z.of_nat n <= two64 ->
  (forall i, 0 <= i < Z.of_nat n -> rd1 SEGS m (Z_to_bv 64 (a + i)) <> None) -> exists bs, rdn SEGS m (Z_to_bv 64 a) n = Some bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n. revert a. induction n as [|n IH]; intros a Ha Hn H; [exists []; reflexivity|].
  cbn [rdn]. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rd1 in H0.
  rewrite zbv_add1. destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs).
  { intros i Hi. rewrite <- Z.add_assoc. apply H. lia. }
  rewrite Hbs. destruct (m (Z_to_bv 64 a)) as [b|]; [eexists; reflexivity|].
  destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|]; [eexists; reflexivity | exfalso; apply H0; reflexivity].
Qed.

#[using="Type"] Lemma lden_sp : forall E x c, 0 <= bv_unsigned (E x) + c < two64 -> bv_unsigned (lden E (laddc (lvar x) c)) = bv_unsigned (E x) + c.
Proof. LiaFast.lf_pins LiaFast.u0. intros E x c H. rewrite lden_laddc, lden_lvar. apply u_small64. exact H. Qed.
End PutApp.

Lemma rg_rw_pt : forall E m R x, rg_ok SEGS E m R -> wkind (rg_kind R) = true ->
  bv_unsigned (lden E (rg_base R)) <= x < bv_unsigned (lden E (rg_base R)) + rsz E R ->
  rd1 SEGS m (Z_to_bv 64 x) <> None /\ wview SEGS m (Z_to_bv 64 x) <> None.
Proof.
  intros E m R x HR Hk Hx. pose proof (rg_ok_rw_byte SEGS E m R HR Hk (x - bv_unsigned (lden E (rg_base R))) ltac:(lia)) as X.
  replace (bv_unsigned (lden E (rg_base R)) + (x - bv_unsigned (lden E (rg_base R)))) with x in X by lia. exact X.
Qed.
Lemma rsz_lconst : forall E n, 0 <= n < two64 -> rsz E (RG (lconst 0) (lconst n) RW TEmpty) = n.
Proof. intros E n Hn. unfold rsz. cbn [rg_size]. rewrite lden_lconst. apply u_small64. exact Hn. Qed.

Lemma kall_cases : forall r, existsb (Pos.eqb (rkey r)) KALLk = true ->
  exists k : nat, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat /\ r = Z_to_bv 5 (Z.of_nat k).
Proof.
  intros r Hr. apply existsb_exists in Hr as (key & Hkey & Hke). apply Pos.eqb_eq in Hke.
  unfold KALLk in Hkey. apply in_map_iff in Hkey as (z & Hz & Hin).
  assert (Hr : r = Z_to_bv 5 z) by (rewrite <- (rkey_reg r), Hke, <- Hz; exact (rkey_reg (Z_to_bv 5 z))).
  exists (Z.to_nat z). cbn [In] in Hin.
  repeat destruct Hin as [<-|Hin]; try destruct Hin; (split; [cbn [In]; repeat (first [left; reflexivity | right]) | exact Hr]).
Qed.
Lemma kall_other : forall k : nat, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> k <> 2%nat ->
  In k [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Proof.
  intros k H1 H2. cbn [In] in H1.
  repeat destruct H1 as [<-|H1]; try destruct H1; first [exfalso; apply H2; reflexivity | cbn [In]; repeat (first [left; reflexivity | right])].
Qed.
Lemma grows_rw : forall segs m m' x, mem_grows m m' -> rd1 segs m x <> None -> wview segs m x <> None ->
  rd1 segs m' x <> None /\ wview segs m' x <> None.
Proof.
  intros segs m m' x Hg H1 H2. unfold rd1, wview in *. destruct (m x) as [b|] eqn:Em.
  - assert (Hm' : m' x <> None) by (apply Hg; rewrite Em; discriminate). destruct (m' x); [split; discriminate | exfalso; apply Hm'; reflexivity].
  - destruct (m' x); [split; discriminate | split; assumption].
Qed.

Section PutMain.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap SEGS.

(* [comment removed for export] *)
Record put_shape (L : sst) (xsz : positive) (iA1 iFt iRO : nat) (lo hi : Z) : Prop := {
  ps_pc   : s_pc L = 0x81f88 ;
  ps_rsv  : s_resv L = RNone ;
  ps_sp   : rget (s_regs L) (rk 2) = laddc (lvar 2) (-2272) ;
  ps_tr   : rget (s_regs L) (rk 10) = laddc (lvar 2) (-2112) ;
  ps_sz   : rget (s_regs L) (rk 11) = lvar xsz ;
  ps_a1   : exists c, nth_error (s_rgs L) iA1 = Some (RG (laddc (lvar 2) (-4320)) (lconst 2048) RW c) ;
  ps_f    : exists c, nth_error (s_rgs L) iFt = Some (RG (laddc (lvar 2) (-2112)) (lconst 240) RW c) ;
  ps_ro   : nth_error (s_rgs L) iRO = Some (RG (lconst 65536) (lconst 77824) RO TEmpty) ;
  ps_fsz  : In (FRange (lvar xsz) 1 30) (s_facts L) ;
  ps_fal  : In (FMod (lvar 2) 4 0) (s_facts L) ;
  ps_frg  : In (FRange (lvar 2) lo hi) (s_facts L) ;
  ps_rng  : 2^46 + 8192 <= lo /\ hi <= 2^47
}.

End PutMain.
End AcPutApp.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcTbl.

Module AcTblOk.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxImg FxStep FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcTbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Lemma ATBLd_ok : tbl_ok ASEGS ATBLd. Proof. apply mk_tbl_ranges_ok. Qed.
Lemma ATBLd_ecall : ecall_ok ASEGS ATBLd. Proof. apply mk_tbl_ranges_ecall. Qed.
Lemma mk_img_runs_ok : forall rs t, Forall (fun p => 0 <= fst p) rs -> img_ok ASEGS t -> img_ok ASEGS (mk_img_runs rs t).
Proof.
  induction rs as [|[lo n] rs IH]; intros t Hrs Ht; cbn [mk_img_runs]; [exact Ht|].
  inversion Hrs as [|? ? Hp Hrs']; subst. apply IH; [exact Hrs'|]. apply mk_img_acc_ok; [|exact Ht].
  cbn [fst] in Hp. apply Z.shiftr_nonneg. exact Hp.
Qed.
Lemma AIMGd_ok : img_ok ASEGS AIMGd.
Proof.
  apply mk_img_runs_ok; [|intros p w Hp; rewrite tget_empty in Hp; discriminate].
  assert (H : forallb (fun p => Z.leb 0 (fst p)) A_WR = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. rewrite Forall_forall. intros p Hp. apply Z.leb_le. exact (H p Hp).
Qed.
End AcTblOk.

Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcComm OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcTblOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rdn_rd1 : forall m (a : Z) n bs j, 0 <= a -> a + Z.of_nat n <= 2^64 -> rdn SEGS m (wa a) n = Some bs -> (j < n)%nat ->
  rd1 SEGS m (Z_to_bv 64 (a + Z.of_nat j)) = nth_error bs j.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a bs j Ha Hn H Hj; [lia|].
  cbn [rdn] in H. destruct (match m (wa a) with Some b => Some b | None => seg_rom SEGS (wa a) end) as [b|] eqn:Eb; [|discriminate].
  destruct (rdn SEGS m (wa a + 1) n) as [rest|] eqn:Er; [|discriminate]. injection H as <-.
  destruct j as [|j].
  - rewrite Z.add_0_r. unfold rd1. exact Eb.
  - assert (Ea : (wa a + 1)%bv = wa (a + 1)) by (unfold wa; apply zbv_add1).
    rewrite Ea in Er. rewrite Nat2Z.inj_succ in Hn.
    replace (a + Z.of_nat (Datatypes.S j)) with ((a + 1) + Z.of_nat j) by lia.
    cbn [nth_error]. exact (IH (a + 1) rest j ltac:(lia) ltac:(lia) Er ltac:(lia)).
Qed.

Lemma rdn_of_rd1 : forall m bs (a : Z), 0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  (forall j, (j < length bs)%nat -> rd1 SEGS m (Z_to_bv 64 (a + Z.of_nat j)) = nth_error bs j) ->
  rdn SEGS m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m bs. induction bs as [|b bs IH]; intros a Ha Hn H; [reflexivity|].
  cbn [length rdn]. pose proof (H O ltac:(cbn [length]; lia)) as H0. rewrite Z.add_0_r in H0. unfold rd1 in H0. cbn [nth_error] in H0.
  rewrite H0. rewrite zbv_add1. cbn [length] in Hn. rewrite (IH (a + 1)); [reflexivity | lia | lia |].
  intros j Hj. specialize (H (Datatypes.S j) ltac:(cbn [length]; lia)). cbn [nth_error] in H. rewrite <- H.
  f_equal. f_equal. lia.
Qed.

Lemma seg_rom_stack : forall x : word, 2^46 <= bv_unsigned x -> seg_rom SEGS x = None.
Proof.
  intros x Hx. apply (seg_rom_above SEGS (2^46) x); [|exact Hx].
  vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vis_of_rd1 : forall (H : word -> bool) m x, rd1 SEGS (mrestrict H m) x <> None -> seg_rom SEGS x = None -> H x = false.
Proof. intros H m x Hr Hs. unfold rd1, mrestrict in Hr. destruct (H x); [rewrite Hs in Hr; exfalso; apply Hr; reflexivity | reflexivity]. Qed.
Lemma rd1_mrestrict_vis : forall (H : word -> bool) m x, H x = false -> rd1 SEGS (mrestrict H m) x = rd1 SEGS m x.
Proof. intros H m x Hx. unfold rd1, mrestrict. rewrite Hx. reflexivity. Qed.

Lemma empty_at_nth_fwd : forall W rgs i j R, nth_error rgs j = Some R ->
  nth_error (empty_at W i rgs) j = Some (if existsb (Nat.eqb (i + j)) W then empty_rg R else R).
Proof.
  intros W rgs. induction rgs as [|R0 rs IH]; intros i j R H; [destruct j; discriminate|].
  destruct j as [|j]; cbn [empty_at nth_error] in *.
  - injection H as <-. rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (Datatypes.S i) j R H). replace (Datatypes.S i + j)%nat with (i + Datatypes.S j)%nat by lia. reflexivity.
Qed.

Lemma put_bytes_shift : forall n bvs t o, tmap (bshift n) (put_bytes t o bvs) = put_bytes (tmap (bshift n) t) o (List.map (bshift n) bvs).
Proof.
  intros n bvs. induction bvs as [|v bvs IH]; intros t o; [reflexivity|].
  cbn [put_bytes List.map]. rewrite IH, tmap_tset. reflexivity.
Qed.
Lemma upd_nth_app : forall l1 l2 i R, (i < length l1)%nat -> upd_nth (l1 ++ l2) i R = upd_nth l1 i R ++ l2.
Proof.
  induction l1 as [|R0 l1 IH]; intros l2 i R Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [app upd_nth]. f_equal. apply IH. cbn in Hi. lia.
Qed.
Lemma upd_nth_map : forall (f : region -> region) l i R, List.map f (upd_nth l i R) = upd_nth (List.map f l) i (f R).
Proof.
  induction l as [|R0 l IH]; intros i R; [destruct i; reflexivity|].
  destruct i as [|i]; [reflexivity|]. cbn [List.map upd_nth]. f_equal. apply IH.
Qed.
Lemma put_rg_next0 : forall S i o bvs, s_next (put_rg S i o bvs) = s_next S.
Proof. intros S i o bvs. unfold put_rg. destruct (nth_error (s_rgs S) i); reflexivity. Qed.
Lemma put_rg_mrg : forall n L S i o bvs, (i < length (s_rgs L))%nat ->
  put_rg (mrg (sst_shift n L) S) i o (List.map (bshift n) bvs) = mrg (sst_shift n (put_rg L i o bvs)) S.
Proof.
  intros n L S i o bvs Hi. unfold put_rg. cbn [mrg sst_shift s_rgs].
  rewrite nth_error_app1 by (rewrite length_map; exact Hi).
  rewrite nth_error_map. destruct (nth_error (s_rgs L) i) as [R|] eqn:HR; [|exfalso; apply nth_error_None in HR; lia].
  cbn [option_map mrg sst_shift s_pc s_regs s_rgs s_facts s_next s_resv].
  rewrite upd_nth_app by (rewrite length_map; exact Hi). unfold mrg, sst_shift. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. rewrite upd_nth_map.
  unfold rshift. cbn [rg_base rg_size rg_kind rg_cont]. rewrite put_bytes_shift. reflexivity.
Qed.

Lemma frz_pt_agree : forall n E E' M w, sm_wf n M = true -> agree n E E' -> (frz_pt E' M w <-> frz_pt E M w).
Proof.
  intros n E E' M w Hwf Ha. pose proof (sm_wf_frz _ M Hwf) as Hfw. rewrite Forall_forall in Hfw. unfold frz_pt.
  split; intros (q & Hq & Hw); exists q; split; [exact Hq| |exact Hq|]; destruct (Hfw q Hq) as [H1 H2];
    unfold uE in *; rewrite ?(lden_agree_wf _ E E' _ H1 Ha), ?(lden_agree_wf _ E E' _ H2 Ha) in *; exact Hw.
Qed.

(* [comment removed for export] *)
Definition unw_res (L : sst) (W : list nat) (iS : nat) : sst :=
  let Lh := hand_post L 0x82a34 KALLk W in
  add_fact (put_rg (bump Lh (Pos.succ (s_next Lh))) iS 0 (bvs_of (lvar (s_next Lh)) 8)) (FRange (lvar (s_next Lh)) 1 30).

Definition TOPL (xt1 xt2 : positive) : lin := LIN 4096 [(xt1, 32768); (xt2, 4096)].
Definition BOTL (xt1 xt2 : positive) : lin := LIN 18446744073701167104 [(xt1, 32768); (xt2, 4096)].
Definition PSZB : list Z := [0; 16; 0; 0; 0; 0; 0; 0].
Definition psz_ok (c : tree bval) (off : Z) : bool :=
  forallb (fun j => match tget (Pos.of_succ_nat (Z.to_nat off + j)) c with Some (BK v) => Z.eqb v (nth j PSZB 0) | _ => false end) (seq 0 8).
Definition PSZC : tree bval := put_list TEmpty [(1%positive, BK 0); (2%positive, BK 16); (3%positive, BK 0); (4%positive, BK 0);
                                                (5%positive, BK 0); (6%positive, BK 0); (7%positive, BK 0); (8%positive, BK 0)].

(* [comment removed for export] *)
Record unw_shape (L : sst) (osp obuf blo zlo bhi zhi : Z) (iLo iF iS iT iHi iRO iGOT iPSZ : nat) (xt1 xt2 : positive) (lo hi : Z) : Prop := {
  us_pc  : s_pc L = 0x82914 ;
  us_rsv : s_resv L = RNone ;
  us_sp  : rget (s_regs L) (rk 2) = laddc (lvar 2) osp ;
  us_buf : rget (s_regs L) (rk 10) = laddc (lvar 2) obuf ;
  us_bp  : rget (s_regs L) (rk 12) = lvar 2 ;
  us_top : rget (s_regs L) (rk 13) = TOPL xt1 xt2 ;
  us_bot : rget (s_regs L) (rk 14) = BOTL xt1 xt2 ;
  us_max : rget (s_regs L) (rk 15) = lconst 30 ;
  us_rlo : exists c, nth_error (s_rgs L) iLo = Some (RG (laddc (lvar 2) blo) (lconst zlo) RW c) ;
  us_rf  : exists c, nth_error (s_rgs L) iF = Some (RG (laddc (lvar 2) (osp - 64)) (lconst 64) RW c) ;
  us_rs  : exists c, nth_error (s_rgs L) iS = Some (RG (laddc (lvar 2) (obuf + 8)) (lconst 8) RW c) /\
           forall j, (4 <= j < 8)%nat -> tget (Pos.of_succ_nat j) c = Some (BK 0) ;
  us_rt  : exists c, nth_error (s_rgs L) iT = Some (RG (laddc (lvar 2) (obuf + 16)) (lconst 240) RW c) ;
  us_rhi : exists c, nth_error (s_rgs L) iHi = Some (RG (laddc (lvar 2) bhi) (lconst zhi) RW c) ;
  us_ro  : nth_error (s_rgs L) iRO = Some (RG (lconst 65536) (lconst 77824) RO TEmpty) ;
  us_got : nth_error (s_rgs L) iGOT = Some (RG (lconst 901120) (lconst 8192) RI TEmpty) ;
  us_psz : exists b z c, nth_error (s_rgs L) iPSZ = Some (RG (lconst b) (lconst z) RZ c) /\ 0 <= b <= 1525856 /\ 1525856 + 8 <= b + z /\
           b + z < two64 /\ psz_ok c (1525856 - b) = true ;
  us_fal : In (FMod (lvar 2) 4 0) (s_facts L) ;
  us_frg : In (FRange (lvar 2) lo hi) (s_facts L) ;
  us_ft1 : In (FRange (lvar xt1) 4294901759 4294967295) (s_facts L) ;
  us_ft2 : In (FRange (lvar xt2) 0 7) (s_facts L) ;
  us_nx  : (2 < s_next L)%positive ;
  us_num : 2^46 + 8192 <= lo /\ hi <= 2^47 /\ osp mod 16 = 0 /\ obuf mod 8 = 0 /\ osp <= obuf /\ obuf + 2056 <= 0 /\
           -8192 <= blo /\ blo <= osp - 1024 /\ osp - 64 <= blo + zlo /\ 0 <= zlo /\ bhi <= obuf + 256 /\ obuf + 2056 <= bhi + zhi /\
           0 <= zhi /\ bhi + zhi <= 0 /\ -8192 <= osp - 1024 /\ blo + zlo <= 0 /\ -8192 <= bhi
}.

Lemma rd1_tracked : forall E m R A j b, rg_ok SEGS E m R -> bv_unsigned (lden E (rg_base R)) = A ->
  tget (Pos.of_succ_nat j) (rg_cont R) = Some (BK b) -> rd1 SEGS m (Z_to_bv 64 (A + Z.of_nat j)) = Some (Z_to_bv 8 b).
Proof.
  intros E m R A j b HR HA Ht. destruct HR as (_ & _ & _ & HT). destruct (HT _ _ Ht) as [_ X]. rewrite HA in X.
  rewrite Zpos_P_of_succ_nat in X. replace (Z.succ (Z.of_nat j) - 1) with (Z.of_nat j) in X by lia. exact X.
Qed.
Lemma nth_bvs_shift : forall n x j b, nth_error (List.map (bshift n) (bvs_of (lvar x) 8)) j = Some b ->
  (j < 8)%nat /\ b = BV (lvar (n + x)) (Z.of_nat j).
Proof.
  intros n x j b H. destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; cbn in H; try (injection H as <-; split; [lia | reflexivity]).
  rewrite nth_error_nil in H. discriminate.
Qed.
Lemma existsb_mid : forall a b c : nat, existsb (Nat.eqb b) [a; b; c] = true.
Proof. intros a b c. apply existsb_exists. exists b. split; [right; left; reflexivity | apply Nat.eqb_refl]. Qed.

Lemma unw_res_mrg : forall n L S W iS, (iS < length (s_rgs L))%nat ->
  mrg (sst_shift n (unw_res L W iS)) S =
  add_fact (put_rg (bump (mrg (sst_shift n (hand_post L 0x82a34 KALLk W)) S) (n + Pos.succ (s_next L + 33))) iS 0
                   (List.map (bshift n) (bvs_of (lvar (s_next L + 33)) 8)))
           (fshift n (FRange (lvar (s_next L + 33)) 1 30)).
Proof.
  intros n L S W iS Hi. unfold unw_res. cbn [hand_post s_next].
  change (mrg (sst_shift n (add_fact ?X ?f)) S) with (add_fact (mrg (sst_shift n X) S) (fshift n f)). f_equal.
  rewrite <- put_rg_mrg; [reflexivity|]. cbn [bump hand_post s_rgs]. rewrite length_empty_at. exact Hi.
Qed.

Lemma zbv8_land : forall x, Z_to_bv 8 (Z.land x 255) = Z_to_bv 8 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. change (2 ^ Z.of_N 8) with (2 ^ 8). rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma reg_sp_off : forall E n L S ms k c SPv, sden0 SEGS E (mrg (sst_shift n L) S) ms -> rget (s_regs L) (rk k) = laddc (lvar 2) c ->
  bv_unsigned (E (n + 2)%positive) = SPv -> 0 <= SPv + c < two64 -> getr (ms_regs ms) (Z_to_bv 5 k) = wa (SPv + c).
Proof.
  intros E n L S ms k c SPv Hd Hl HS Hr. rewrite (mrg_reg E n L S ms (Z_to_bv 5 k) _ Hd Hl). unfold wa. apply bv_eq.
  rewrite lden_sp; unfold vshift; rewrite HS; [|exact Hr]. rewrite u_small64 by exact Hr. reflexivity.
Qed.
Lemma reg_lin2 : forall E n L S ms k c x1 k1 x2 k2 v, sden0 SEGS E (mrg (sst_shift n L) S) ms -> rget (s_regs L) (rk k) = LIN c [(x1, k1); (x2, k2)] ->
  eqm (c + k1 * bv_unsigned (E (n + x1)%positive) + k2 * bv_unsigned (E (n + x2)%positive)) v -> getr (ms_regs ms) (Z_to_bv 5 k) = wa v.
Proof.
  intros E n L S ms k c x1 k1 x2 k2 v Hd Hl Hv. rewrite (mrg_reg E n L S ms (Z_to_bv 5 k) _ Hd Hl). unfold lden, lz. cbn [l_c l_t tsum]. unfold vz, vshift, wa.
  apply Z_to_bv_eqm. replace (c + (k1 * bv_unsigned (E (n + x1)%positive) + (k2 * bv_unsigned (E (n + x2)%positive) + 0))) with
    (c + k1 * bv_unsigned (E (n + x1)%positive) + k2 * bv_unsigned (E (n + x2)%positive)) by ring. exact Hv.
Qed.

Lemma stk_rw : forall E m b z c SPv x, rg_ok SEGS E m (RG (laddc (lvar 2) b) (lconst z) RW c) -> bv_unsigned (E 2%positive) = SPv ->
  8192 <= SPv <= 2^47 -> -8192 <= b -> 0 <= z -> b + z <= 0 -> SPv + b <= x < SPv + b + z ->
  rd1 SEGS m (Z_to_bv 64 x) <> None /\ wview SEGS m (Z_to_bv 64 x) <> None.
Proof.
  intros E m b z c SPv x HR HS HSr Hb Hz Hbz Hx. apply (rg_rw_pt _ _ _ x HR eq_refl). cbn [rg_base].
  rewrite lden_sp; rewrite HS; [|unfold two64; lia]. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia.
Qed.
Lemma stk_in : forall E b z c SPv x, bv_unsigned (E 2%positive) = SPv ->
  8192 <= SPv <= 2^47 -> -8192 <= b -> 0 <= z -> b + z <= 0 -> SPv + b <= bv_unsigned x < SPv + b + z ->
  in_rg E (RG (laddc (lvar 2) b) (lconst z) RW c) x.
Proof.
  intros E b z c SPv x HS HSr Hb Hz Hbz Hx. unfold in_rg. cbn [rg_base].
  rewrite lden_sp; rewrite HS; [|unfold two64; lia]. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). lia.
Qed.

Lemma unw_wr : forall E m SPv osp obuf blo zlo bhi zhi clo cf cs ct chi, bv_unsigned (E 2%positive) = SPv -> 8192 <= SPv <= 2^47 ->
  osp <= obuf -> obuf + 2056 <= 0 -> -8192 <= blo -> blo <= osp - 1024 -> osp - 64 <= blo + zlo -> 0 <= zlo -> blo + zlo <= 0 ->
  -8192 <= bhi -> bhi <= obuf + 256 -> obuf + 2056 <= bhi + zhi -> 0 <= zhi -> bhi + zhi <= 0 -> -8192 <= osp - 1024 ->
  rg_ok SEGS E m (RG (laddc (lvar 2) blo) (lconst zlo) RW clo) ->
  rg_ok SEGS E m (RG (laddc (lvar 2) (osp - 64)) (lconst 64) RW cf) ->
  rg_ok SEGS E m (RG (laddc (lvar 2) (obuf + 8)) (lconst 8) RW cs) ->
  rg_ok SEGS E m (RG (laddc (lvar 2) (obuf + 16)) (lconst 240) RW ct) ->
  rg_ok SEGS E m (RG (laddc (lvar 2) bhi) (lconst zhi) RW chi) ->
  forall x, (SPv + osp - 1024 <= x < SPv + osp) \/ (SPv + obuf + 8 <= x < SPv + obuf + 2056) ->
  rd1 SEGS m (Z_to_bv 64 x) <> None /\ wview SEGS m (Z_to_bv 64 x) <> None.
Proof.
  intros E m SPv osp obuf blo zlo bhi zhi clo cf cs ct chi HS HSr N5 N6 N7 N8 N9 N10 N16 N17 N11 N12 N13 N14 N15 Rlo Rf Rs Rt Rhi x Hx.
  destruct (Z_lt_ge_dec x (SPv + osp - 64)) as [H1|H1]; [apply (stk_rw E m blo zlo clo SPv x Rlo HS); lia|].
  destruct (Z_lt_ge_dec x (SPv + osp)) as [H2|H2]; [apply (stk_rw E m (osp - 64) 64 cf SPv x Rf HS); lia|].
  destruct (Z_lt_ge_dec x (SPv + obuf + 16)) as [H3|H3]; [apply (stk_rw E m (obuf + 8) 8 cs SPv x Rs HS); lia|].
  destruct (Z_lt_ge_dec x (SPv + obuf + 256)) as [H4|H4]; [apply (stk_rw E m (obuf + 16) 240 ct SPv x Rt HS); lia|].
  apply (stk_rw E m bhi zhi chi SPv x Rhi HS); lia.
Qed.

Lemma ro_none : forall E m, rg_ok SEGS E m (RG (lconst 65536) (lconst 77824) RO TEmpty) ->
  forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.
Proof.
  intros E m Rro i Hi. destruct Rro as (_ & _ & Hb & _). cbn [rg_base rg_kind rg_size] in Hb. unfold rsz in Hb. cbn [rg_size] in Hb.
  rewrite lden_lconst, u_small64 in Hb by (unfold two64; lia). specialize (Hb (i - 65536) ltac:(lia)).
  rewrite lden_lconst, u_small64 in Hb by (unfold two64; lia). replace (65536 + (i - 65536)) with i in Hb by lia. exact (proj1 Hb).
Qed.
Lemma got_word : forall E m, rg_ok SEGS E m (RG (lconst 901120) (lconst 8192) RI TEmpty) ->
  rdn SEGS m (wa 904176) 8 = Some (word_to_le_bytes 8 (wa 1525856)).
Proof.
  intros E m Rgot. assert (Hl : length (word_to_le_bytes 8 (wa 1525856)) = 8%nat) by reflexivity.
  rewrite <- Hl. unfold wa at 1. apply rdn_of_rd1; [lia | rewrite Hl; unfold two64; lia |].
  intros j Hj. rewrite Hl in Hj.
  destruct Rgot as (_ & _ & Hb & _). cbn [rg_base rg_kind rg_size rg_cont] in Hb. unfold rsz in Hb. cbn [rg_size] in Hb.
  rewrite lden_lconst, u_small64 in Hb by (unfold two64; lia).
  specialize (Hb (3056 + Z.of_nat j) ltac:(lia)). rewrite lden_lconst, u_small64 in Hb by (unfold two64; lia).
  destruct Hb as (_ & Hb). rewrite tget_empty in Hb. specialize (Hb eq_refl).
  replace (901120 + (3056 + Z.of_nat j)) with (904176 + Z.of_nat j) in Hb by lia. rewrite Hb.
  pose proof AIMGd_ok as Himg. unfold img_ok in Himg.
  assert (Ht : tget 113023%positive AIMGd = Some 1525856) by (vm_compute; reflexivity).
  specialize (Himg _ _ Ht (Z.of_nat j) ltac:(lia)). replace (8 * (Zpos 113023 - 1) + Z.of_nat j) with (904176 + Z.of_nat j) in Himg by lia.
  rewrite Himg. unfold word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hj. rewrite u_wa_small by lia. rewrite zbv8_land. reflexivity.
Qed.
Lemma got_word_g : forall E m k b z, (k = RI \/ k = RO) -> 0 <= b <= 904176 -> 904184 <= b + z <= 2^47 ->
  rg_ok SEGS E m (RG (lconst b) (lconst z) k TEmpty) -> rdn SEGS m (wa 904176) 8 = Some (word_to_le_bytes 8 (wa 1525856)).
Proof.
  intros E m k b z Hk Hb Hz Rgot. assert (Hl : length (word_to_le_bytes 8 (wa 1525856)) = 8%nat) by reflexivity.
  rewrite <- Hl. unfold wa at 1. apply rdn_of_rd1; [lia | rewrite Hl; unfold two64; lia |].
  intros j Hj. rewrite Hl in Hj.
  destruct Rgot as (_ & _ & Hr & _). cbn [rg_base rg_kind rg_size rg_cont] in Hr. unfold rsz in Hr. cbn [rg_size] in Hr.
  rewrite lden_lconst, u_small64 in Hr by (unfold two64; lia).
  specialize (Hr (904176 - b + Z.of_nat j) ltac:(lia)). rewrite lden_lconst, u_small64 in Hr by (unfold two64; lia).
  assert (Hb' : rd1 SEGS m (Z_to_bv 64 (b + (904176 - b + Z.of_nat j))) = seg_rom SEGS (Z_to_bv 64 (b + (904176 - b + Z.of_nat j)))).
  { destruct Hk as [Ek|Ek]; subst k.
    - destruct Hr as (_ & Hr). rewrite tget_empty in Hr. exact (Hr eq_refl).
    - destruct Hr as (Hn & _). unfold rd1. rewrite Hn. reflexivity. }
  clear Hr. rename Hb' into Hr.
  replace (b + (904176 - b + Z.of_nat j)) with (904176 + Z.of_nat j) in Hr by lia. rewrite Hr.
  pose proof AIMGd_ok as Himg. unfold img_ok in Himg.
  assert (Ht : tget 113023%positive AIMGd = Some 1525856) by (vm_compute; reflexivity).
  specialize (Himg _ _ Ht (Z.of_nat j) ltac:(lia)). replace (8 * (Zpos 113023 - 1) + Z.of_nat j) with (904176 + Z.of_nat j) in Himg by lia.
  rewrite Himg. unfold word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hj. rewrite u_wa_small by lia. rewrite zbv8_land. reflexivity.
Qed.
Lemma got_word_k : forall E m k, (k = RI \/ k = RO) -> rg_ok SEGS E m (RG (lconst 901120) (lconst 8192) k TEmpty) ->
  rdn SEGS m (wa 904176) 8 = Some (word_to_le_bytes 8 (wa 1525856)).
Proof.
  intros E m k Hk Rgot. assert (Hl : length (word_to_le_bytes 8 (wa 1525856)) = 8%nat) by reflexivity.
  rewrite <- Hl. unfold wa at 1. apply rdn_of_rd1; [lia | rewrite Hl; unfold two64; lia |].
  intros j Hj. rewrite Hl in Hj.
  destruct Rgot as (_ & _ & Hb & _). cbn [rg_base rg_kind rg_size rg_cont] in Hb. unfold rsz in Hb. cbn [rg_size] in Hb.
  rewrite lden_lconst, u_small64 in Hb by (unfold two64; lia).
  specialize (Hb (3056 + Z.of_nat j) ltac:(lia)). rewrite lden_lconst, u_small64 in Hb by (unfold two64; lia).
  assert (Hb' : rd1 SEGS m (Z_to_bv 64 (901120 + (3056 + Z.of_nat j))) = seg_rom SEGS (Z_to_bv 64 (901120 + (3056 + Z.of_nat j)))).
  { destruct Hk as [Ek|Ek]; subst k.
    - destruct Hb as (_ & Hb). rewrite tget_empty in Hb. exact (Hb eq_refl).
    - destruct Hb as (Hn & _). unfold rd1. rewrite Hn. reflexivity. }
  clear Hb. rename Hb' into Hb.
  replace (901120 + (3056 + Z.of_nat j)) with (904176 + Z.of_nat j) in Hb by lia. rewrite Hb.
  pose proof AIMGd_ok as Himg. unfold img_ok in Himg.
  assert (Ht : tget 113023%positive AIMGd = Some 1525856) by (vm_compute; reflexivity).
  specialize (Himg _ _ Ht (Z.of_nat j) ltac:(lia)). replace (8 * (Zpos 113023 - 1) + Z.of_nat j) with (904176 + Z.of_nat j) in Himg by lia.
  rewrite Himg. unfold word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hj. rewrite u_wa_small by lia. rewrite zbv8_land. reflexivity.
Qed.
Lemma psz_word : forall E m b z c, rg_ok SEGS E m (RG (lconst b) (lconst z) RZ c) -> 0 <= b <= 1525856 -> 1525856 + 8 <= b + z ->
  b + z < two64 -> psz_ok c (1525856 - b) = true -> rdn SEGS m (wa 1525856) 8 = Some (word_to_le_bytes 8 (wa 4096)).
Proof.
  intros E m b z c Rpsz Hb Hz Hz64 Hok. assert (Hl : length (word_to_le_bytes 8 (wa 4096)) = 8%nat) by reflexivity.
  rewrite <- Hl. unfold wa at 1. apply rdn_of_rd1; [lia | rewrite Hl; unfold two64; lia |].
  intros j Hj. rewrite Hl in Hj.
  assert (HA : bv_unsigned (lden E (rg_base (RG (lconst b) (lconst z) RZ c))) = b).
  { cbn [rg_base]. rewrite lden_lconst, u_small64 by (unfold two64 in *; lia). reflexivity. }
  unfold psz_ok in Hok. rewrite forallb_forall in Hok. specialize (Hok j ltac:(apply in_seq; lia)).
  destruct (tget (Pos.of_succ_nat (Z.to_nat (1525856 - b) + j)) c) as [[v|l jj]|] eqn:Ht; try discriminate. apply Z.eqb_eq in Hok.
  pose proof (rd1_tracked E m _ b (Z.to_nat (1525856 - b) + j) v Rpsz HA Ht) as X.
  replace (b + Z.of_nat (Z.to_nat (1525856 - b) + j)) with (1525856 + Z.of_nat j) in X by lia. rewrite X.
  unfold word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hj. rewrite u_wa_small by lia. rewrite Hok.
  do 8 (destruct j as [|j]; [f_equal; apply bv_eq; vm_compute; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma unw_uch1 : forall m E SPv TOP V8 c, rg_ok SEGS E m (RG (laddc (lvar 2) (-56)) (lconst 56) RW c) -> bv_unsigned (E 2%positive) = SPv ->
  8192 <= SPv <= 2^47 -> TOP <= 2^47 -> bv_unsigned (E 8%positive) = V8 ->
  (forall j, (j < 8)%nat -> tget (Pos.of_succ_nat (40 + j)) c = Some (BV (lvar 8) (Z.of_nat j))) ->
  (V8 <= SPv \/ TOP - 16 <= V8 \/ V8 mod 8 <> 0) -> uch m TOP SPv.
Proof.
  intros m E SPv TOP V8 c HR HS HSr HTr HV Ht HNB.
  assert (Hrw : forall x, SPv - 56 <= x < SPv -> rd1 SEGS m (Z_to_bv 64 x) <> None).
  { intros x Hx. exact (proj1 (stk_rw E m (-56) 56 c SPv x HR HS HSr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }
  apply uch_mk.
  - apply (rdn_some m (SPv - 8) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrw. cbn in Hi. lia.
  - apply (rdn_some m (SPv - 16) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrw. cbn in Hi. lia.
  - intros nb Hrd H1 H2 H3. exfalso.
    assert (HV8 : 0 <= V8 < 2^64) by (rewrite <- HV; apply bv_unsigned_in_range).
    assert (Hrd8 : rd m (SPv - 16) 8 V8).
    { unfold rd, word_to_le_bytes. rewrite u_wa_small by lia.
      assert (Hl : length (Z_to_le_bytes 8 V8) = 8%nat) by apply length_Z_to_le_bytes. rewrite <- Hl.
      unfold wa. apply rdn_of_rd1; [lia | rewrite Hl; unfold two64; lia |]. rewrite Hl. intros j Hj.
      rewrite nth_Z_to_le_bytes by exact Hj.
      assert (HA : bv_unsigned (lden E (rg_base (RG (laddc (lvar 2) (-56)) (lconst 56) RW c))) = SPv - 56).
      { cbn [rg_base]. rewrite lden_sp; rewrite HS; [lia | unfold two64; lia]. }
      destruct HR as (_ & _ & _ & HT). destruct (HT _ _ (Ht j Hj)) as [_ X]. rewrite HA in X.
      rewrite Zpos_P_of_succ_nat, Nat2Z.inj_add in X. replace (SPv - 56 + (Z.succ (Z.of_nat 40 + Z.of_nat j) - 1)) with (SPv - 16 + Z.of_nat j) in X by lia.
      rewrite X. cbn [bden]. rewrite lden_lvar, HV. reflexivity. }
    assert (Hnb : nb = V8).
    { apply (rd_inj m (SPv - 16) 8 nb V8); [lia | | | exact Hrd | exact Hrd8].
      - change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). lia.
      - change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). exact HV8. }
    subst nb. lia.
Qed.

(* [comment removed for export] *)
Fixpoint chain_ok (m : word -> option byte) (top f : Z) (fs : list Z) : Prop :=
  16 <= f <= 2^47 /\ (forall i, f - 16 <= i < f -> rd1 SEGS m (Z_to_bv 64 i) <> None) /\
  match fs with
  | [] => exists v, 0 <= v < 2^64 /\ rd m (f - 16) 8 v /\ (v <= f \/ top - 16 <= v \/ v mod 8 <> 0)
  | f' :: fs' => 0 <= f' < 2^64 /\ rd m (f - 16) 8 f' /\ chain_ok m top f' fs'
  end.
Lemma uch_frames : forall m top fs f, top <= 2^47 -> chain_ok m top f fs -> uch m top f.
Proof.
  intros m top fs. induction fs as [|f' fs IH]; intros f Ht (Hf & Hrw & Hc).
  - destruct Hc as (v & Hv & Hrd & Hinv). apply uch_mk.
    + apply (rdn_some m (f - 8) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrw. cbn in Hi. lia.
    + apply (rdn_some m (f - 16) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrw. cbn in Hi. lia.
    + intros nb Hnb H1 H2 H3. exfalso.
      assert (Hnbv : nb = v) by (apply (rd_inj m (f - 16) 8 nb v); [lia | change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia | change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia | exact Hnb | exact Hrd]).
      subst nb. lia.
  - destruct Hc as (Hv & Hrd & Hc). apply uch_mk.
    + apply (rdn_some m (f - 8) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrw. cbn in Hi. lia.
    + apply (rdn_some m (f - 16) 8); [lia | cbn; unfold two64; lia |]. intros i Hi. apply Hrw. cbn in Hi. lia.
    + intros nb Hnb H1 H2 H3.
      assert (Hnbv : nb = f') by (apply (rd_inj m (f - 16) 8 nb f'); [lia | change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia | change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia | exact Hnb | exact Hrd]).
      subst nb. exact (IH f' Ht Hc).
Qed.

Section UnwMain.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap SEGS.

End UnwMain.
