(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan AXG_put AXG_put2 AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_np.
Import ListNotations AX2 AX2S.

Module AXF_pfl.
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

Definition e_I := EVar 32.
Definition e_EN := EVar 33.
Definition e_UI := EVar 34.
Definition e_NN := EVar 35.
Definition e_SZ := EVar 36.
Definition ST := EAlu ALU_ADD (EMd M_MUL (ELit (-4)) e_I) e_EN.
Definition sr_pfl := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_I)) 11 (e_EN)) 12 (e_UI)) 19 (e_NN)) 21 (e_SZ)).
Definition kn_pfl : list kentry :=
  [ KRange e_I 0 (2^47);
    KRange e_EN 1 (2^47);
    KRange e_UI 0 (2^36);
    KRange e_NN 1 (2^47);
    KRange e_SZ 16 65536;
    KRange ST 5 (2^47);
    KWr (SA ST (-4)) (ELit 4) ].
Definition scr_pfl : scripts := SCR [true] [] [].
Definition ss_pfl := SS 0x449fc sr_pfl [] kn_pfl 37.
Definition RUN_pfl := sym_exec SEGS 12 true [0x449fc; 0x44a1c] scr_pfl ss_pfl [].

Definition scr_ppflc : scripts := SCR [true] [] [].
Definition RES_ppflc := Eval vm_compute in sym_exec SEGS 12 true [0x449fc; 0x44a1c] scr_ppflc ss_pfl [].
Lemma RES_ppflc_ok : sym_exec SEGS 12 true [0x449fc; 0x44a1c] scr_ppflc (SS 0x449fc sr_pfl [] kn_pfl 37) [] = RES_ppflc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_ppflx : scripts := SCR [false] [] [].
Definition RES_ppflx := Eval vm_compute in sym_exec SEGS 12 true [0x449fc; 0x44a1c] scr_ppflx ss_pfl [].
Lemma RES_ppflx_ok : sym_exec SEGS 12 true [0x449fc; 0x44a1c] scr_ppflx (SS 0x449fc sr_pfl [] kn_pfl 37) [] = RES_ppflx.
Proof. vm_compute. reflexivity. Qed.
End AXF_pfl.

Module AXF_pflz.
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

Section PFL.
Context {fx : FPState}.

Definition VALS_pfl (I EN UI NN SZ : Z) : list Z := [I; EN; UI; NN; SZ].

Record pfl_pre (regs : bvmap 5 word) (m : word -> option byte) (I EN UI NN SZ : Z) : Prop := {
  pfl_R10 : getr regs 10 = wa I ;
  pfl_R11 : getr regs 11 = wa EN ;
  pfl_R12 : getr regs 12 = wa UI ;
  pfl_R19 : getr regs 19 = wa NN ;
  pfl_R21 : getr regs 21 = wa SZ ;
  pfl_rng_I : 0 <= I <= 2^47 ;
  pfl_rng_EN : 1 <= EN <= 2^47 ;
  pfl_rng_UI : 0 <= UI <= 2^36 ;
  pfl_rng_NN : 1 <= NN <= 2^47 ;
  pfl_rng_SZ : 16 <= SZ <= 65536 ;
  pfl_kr5 : 5 <= (-4 * I) + EN <= (2^47) ;
  pfl_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa ((-4 * I) + EN + -4 + d)) k = true
}.


#[using="Type"] Lemma pfl_setup : forall regs m I EN UI NN SZ, pfl_pre regs m I EN UI NN SZ ->
  regs_ok (Ez regs (VALS_pfl I EN UI NN SZ)) AXF_pfl.sr_pfl regs /\ know_ok SEGS (Ez regs (VALS_pfl I EN UI NN SZ)) m AXF_pfl.kn_pfl.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m I EN UI NN SZ P. destruct P as [pfl_R10 pfl_R11 pfl_R12 pfl_R19 pfl_R21 pfl_rng_I pfl_rng_EN pfl_rng_UI pfl_rng_NN pfl_rng_SZ pfl_kr5 pfl_kwr6].
  set (E := Ez regs (VALS_pfl I EN UI NN SZ)).
  assert (Z32 : bv_unsigned (ev E 32) = I) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = UI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).

  split.
  { unfold AXF_pfl.sr_pfl.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|].
    - rewrite pfl_R10. reflexivity.
    - rewrite pfl_R11. reflexivity.
    - rewrite pfl_R12. reflexivity.
    - rewrite pfl_R19. reflexivity.
    - rewrite pfl_R21. reflexivity. }
  unfold know_ok, AXF_pfl.kn_pfl.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pfl.e_I AXF_pfl.e_EN AXF_pfl.e_UI AXF_pfl.e_NN AXF_pfl.e_SZ AXF_pfl.ST a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range I _ _ pfl_rng_I eq_refl eq_refl), ?(mod64_of_range EN _ _ pfl_rng_EN eq_refl eq_refl), ?(mod64_of_range UI _ _ pfl_rng_UI eq_refl eq_refl), ?(mod64_of_range NN _ _ pfl_rng_NN eq_refl eq_refl), ?(mod64_of_range SZ _ _ pfl_rng_SZ eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply pfl_kwr6]; assumption).
  all: try (clear - pfl_rng_I pfl_rng_EN pfl_rng_UI pfl_rng_NN pfl_rng_SZ pfl_kr5; lia).
  all: first [lia].
Qed.


Definition pfl_mem_ppflc (m : word -> option byte) (regs : bvmap 5 word) (I EN UI NN SZ : Z) : word -> option byte :=
  wbytes (m) (wa ((-4 * I) + EN + -4)) (word_to_le_bytes 4 (wa (Z.shiftr UI 4))).

#[using="Type"] Theorem pfl_ppflc : forall regs m rom I EN UI NN SZ, pfl_pre regs m I EN UI NN SZ ->
  scs_denot SEGS m (Ez regs (VALS_pfl I EN UI NN SZ)) (snd (fst AXF_pfl.RES_ppflc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x449fc) m rom) (mkst R (wa 0x449fc) (pfl_mem_ppflc m regs I EN UI NN SZ) rom) /\
    getr R 10 = wa (I + 1) /\ getr R 11 = wa EN /\ getr R 12 = wa (UI + SZ) /\ getr R 14 = wa (Z.shiftr UI 4) /\ getr R 15 = wa (((-4 * I) + EN) + -4) /\ getr R 19 = wa NN /\ getr R 21 = wa SZ /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 16; 17; 18; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom I EN UI NN SZ P Hsc. destruct (pfl_setup regs m I EN UI NN SZ P) as [HR HK].
  set (E := Ez regs (VALS_pfl I EN UI NN SZ)) in *. destruct P as [pfl_R10 pfl_R11 pfl_R12 pfl_R19 pfl_R21 pfl_rng_I pfl_rng_EN pfl_rng_UI pfl_rng_NN pfl_rng_SZ pfl_kr5 pfl_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = I) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = UI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 12 [0x449fc; 0x44a1c] AXF_pfl.scr_ppflc 0x449fc AXF_pfl.sr_pfl AXF_pfl.kn_pfl 37 _ _ _ E m rom regs AXF_pfl.RES_ppflc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pfl.RES_ppflc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pfl_mem_ppflc m regs I EN UI NN SZ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pfl_mem_ppflc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition pfl_mem_ppflx (m : word -> option byte) (regs : bvmap 5 word) (I EN UI NN SZ : Z) : word -> option byte :=
  wbytes (m) (wa ((-4 * I) + EN + -4)) (word_to_le_bytes 4 (wa (Z.shiftr UI 4))).

#[using="Type"] Theorem pfl_ppflx : forall regs m rom I EN UI NN SZ, pfl_pre regs m I EN UI NN SZ ->
  scs_denot SEGS m (Ez regs (VALS_pfl I EN UI NN SZ)) (snd (fst AXF_pfl.RES_ppflx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x449fc) m rom) (mkst R (wa 0x44a1c) (pfl_mem_ppflx m regs I EN UI NN SZ) rom) /\
    getr R 10 = wa (I + 1) /\ getr R 11 = wa EN /\ getr R 12 = wa (UI + SZ) /\ getr R 14 = wa (Z.shiftr UI 4) /\ getr R 15 = wa (((-4 * I) + EN) + -4) /\ getr R 19 = wa NN /\ getr R 21 = wa SZ /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 16; 17; 18; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom I EN UI NN SZ P Hsc. destruct (pfl_setup regs m I EN UI NN SZ P) as [HR HK].
  set (E := Ez regs (VALS_pfl I EN UI NN SZ)) in *. destruct P as [pfl_R10 pfl_R11 pfl_R12 pfl_R19 pfl_R21 pfl_rng_I pfl_rng_EN pfl_rng_UI pfl_rng_NN pfl_rng_SZ pfl_kr5 pfl_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = I) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = EN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = UI) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).

  destruct (run_sound SEGS 12 [0x449fc; 0x44a1c] AXF_pfl.scr_ppflx 0x449fc AXF_pfl.sr_pfl AXF_pfl.kn_pfl 37 _ _ _ E m rom regs AXF_pfl.RES_ppflx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pfl.RES_ppflx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pfl_mem_ppflx m regs I EN UI NN SZ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pfl_mem_ppflx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PFL.
End AXF_pflz.

Module AXG_pfl.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan AXG_put AXG_put2 AXG_np.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Local Ltac lenq := rewrite ?length_N_to_le_bytes; change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.
Local Ltac znq := change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.

(* [comment removed for export] *)
Definition KPFL : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Section SCP.
Context {fx : FPState}.
Variables (R : bvmap 5 word) (m : word -> option byte) (I EN UI NN SZ : Z).
Hypothesis HR : 0 <= I <= 2^47 /\ 1 <= EN <= 2^47 /\ 0 <= UI <= 2^36 /\ 1 <= NN <= 2^47 /\ 16 <= SZ <= 65536.
Local Ltac zat := repeat match goal with |- context [bv_unsigned (ev (Ez ?R ?V) ?n)] =>
              let v := eval cbn [nth Nat.sub] in (nth (n - 32) V 0) in rewrite (zatom R V n v eq_refl eq_refl) by slia end.
Local Ltac scb := apply sc_br_z; first [rewrite br_geu_z | rewrite br_ltu_z | rewrite br_eq_z | rewrite br_ne_z];
            cbn [zeval edenot]; zat; rewrite ?(Z.mod_small _ (2^64)) by slia; bfin.
#[using="HR"] Lemma sc_pflc : I + 1 < NN -> scs_denot SEGS m (Ez R (AXF_pflz.VALS_pfl I EN UI NN SZ)) (snd (fst AXF_pfl.RES_ppflc)).
Proof. LiaFast.lf_pins (fun (HR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_pfl.RES_ppflc fst snd]. unfold AXF_pflz.VALS_pfl. scgo; scb. Qed.
#[using="HR"] Lemma sc_pflx : NN <= I + 1 -> scs_denot SEGS m (Ez R (AXF_pflz.VALS_pfl I EN UI NN SZ)) (snd (fst AXF_pfl.RES_ppflx)).
Proof. LiaFast.lf_pins (fun (HR : LiaFast.U) => LiaFast.u0). intros H. cbn [AXF_pfl.RES_ppflx fst snd]. unfold AXF_pflz.VALS_pfl. scgo; scb. Qed.
End SCP.

(* [comment removed for export] *)
Lemma pfl_gen : forall {fx : FPState} rom (k : nat) regs m I EN UI NN SZ,
  (1 <= k)%nat -> NN = I + Z.of_nat k ->
  getr regs 10 = wa I -> getr regs 11 = wa EN -> getr regs 12 = wa UI -> getr regs 19 = wa NN -> getr regs 21 = wa SZ ->
  0 <= I -> 4 * NN + 1 <= EN <= 2^47 -> 0 <= UI -> UI + Z.of_nat k * SZ <= 2^36 -> 16 <= SZ <= 65536 ->
  wr m (EN - 4 * NN) (4 * Z.of_nat k) ->
  exists R m', msteps SEGS (mkst regs (wa 0x449fc) m rom) (mkst R (wa 0x44a1c) m' rom) /\
    getr R 10 = wa NN /\ getr R 12 = wa (UI + Z.of_nat k * SZ) /\
    (forall kk, In kk KPFL -> getr R (Z_to_bv 5 (Z.of_nat kk)) = getr regs (Z_to_bv 5 (Z.of_nat kk))) /\
    (forall j, 0 <= j < Z.of_nat k -> rd m' (EN - 4 * (I + j + 1)) 4 ((UI + j * SZ) / 16)) /\
    (forall x, 0 <= x < 2^64 -> ~ (EN - 4 * NN <= x < EN - 4 * I) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof.
  intros fx rom k. induction k as [|k IH]; intros regs m I EN UI NN SZ Hk HNN H10 H11 H12 H19 H21 HI HEN HU HUS HSZ HWR; [lia|].
  rewrite Nat2Z.inj_succ in *.
  assert (P : AXF_pflz.pfl_pre regs m I EN UI NN SZ).
  { constructor; try assumption; try lia.
    intros d kk Hd Hkk. replace (-4 * I + EN + -4 + d) with (EN - 4 * NN + (4 * Z.of_nat k + d)) by lia. apply HWR; lia. }
  set (m1 := wbytes m (wa (-4 * I + EN + -4)) (word_to_le_bytes 4 (wa (Z.shiftr UI 4)))).
  assert (Hm1c : AXF_pflz.pfl_mem_ppflc m regs I EN UI NN SZ = m1) by reflexivity.
  assert (Hm1x : AXF_pflz.pfl_mem_ppflx m regs I EN UI NN SZ = m1) by reflexivity.
  assert (E1 : forall x, 0 <= x < 2^64 -> ~ (EN - 4 * (I + 1) <= x < EN - 4 * I) -> m1 (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m1. apply wb_other; [exact Hx | lia | lenq; lia | lenq; lia]. }
  assert (R1 : rd m1 (EN - 4 * (I + 1)) 4 (UI / 16)).
  { unfold m1. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    replace (-4 * I + EN + -4) with (EN - 4 * (I + 1)) by lia. apply wb_rd_hit; lia. }
  assert (G1 : mem_grows m m1) by (unfold m1; apply wbytes_grows).
  destruct k as [|k'].
  - (* [comment removed for export] *)
    destruct (AXF_pflz.pfl_ppflx regs m rom I EN UI NN SZ P (sc_pflx regs m I EN UI NN SZ ltac:(lia) ltac:(cbn in *; lia)))
      as (R & Hms & A10 & A11 & A12 & A14 & A15 & A19 & A21 & KK).
    rewrite Hm1x in Hms. exists R, m1. split; [exact Hms|]. cbn [Z.of_nat] in *.
    split; [rewrite A10; f_equal; lia|]. split; [rewrite A12; f_equal; lia|].
    split.
    { intros kk Hkk. cbn [KPFL In] in Hkk.
      repeat (destruct Hkk as [<-|Hkk]; [first [apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ] | (first [transitivity (wa EN); [exact A11 | symmetry; exact H11] | transitivity (wa NN); [exact A19 | symmetry; exact H19] | transitivity (wa SZ); [exact A21 | symmetry; exact H21]])]|]).
      destruct Hkk. }
    split; [intros j Hj; replace j with 0 by lia; replace (I + 0 + 1) with (I + 1) by ring; replace (UI + 0 * SZ) with UI by ring; exact R1|].
    split; [intros x Hx Hn; apply E1; [exact Hx | lia] | exact G1].
  - (* [comment removed for export] *)
    destruct (AXF_pflz.pfl_ppflc regs m rom I EN UI NN SZ P (sc_pflc regs m I EN UI NN SZ ltac:(lia) ltac:(lia)))
      as (R & Hms & A10 & A11 & A12 & A14 & A15 & A19 & A21 & KK).
    rewrite Hm1c in Hms.
    destruct (IH R m1 (I + 1) EN (UI + SZ) NN SZ ltac:(lia) ltac:(lia) A10 A11 A12 A19 A21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R' & m' & Hms' & B10 & B12 & KK' & RD & FR & G').
    { intros d kk Hd Hkk. apply (store_ok_mono SEGS kk m m1 _ G1). apply HWR; lia. }
    exists R', m'. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|].
    split; [exact B10|]. split; [rewrite B12; f_equal; lia|].
    split.
    { intros kk Hkk. rewrite (KK' kk Hkk). cbn [KPFL In] in Hkk.
      repeat (destruct Hkk as [<-|Hkk]; [first [apply KK; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ] | (first [transitivity (wa EN); [exact A11 | symmetry; exact H11] | transitivity (wa NN); [exact A19 | symmetry; exact H19] | transitivity (wa SZ); [exact A21 | symmetry; exact H21]])]|]).
      destruct Hkk. }
    split.
    + intros j Hj. destruct (Z.eq_dec j 0) as [->|Hj0].
      * replace (I + 0 + 1) with (I + 1) by ring. replace (UI + 0 * SZ) with UI by ring.
        apply (rd_frame m1 m'); [lia | cbn; lia | | exact R1]. intros x Hx. znq. apply FR; lia.
      * replace (EN - 4 * (I + j + 1)) with (EN - 4 * (I + 1 + (j - 1) + 1)) by ring.
        replace (UI + j * SZ) with (UI + SZ + (j - 1) * SZ) by ring. apply RD; lia.
    + split; [intros x Hx Hn; rewrite FR by lia; apply E1; lia | exact (mem_grows_trans _ _ _ G1 G')].
Qed.

(* [comment removed for export] *)
Lemma pfa_loop : forall {fx : FPState} rom (N : nat) regs m A K U SZ,
  (1 <= N)%nat -> getr regs 10 = wa 0 -> getr regs 11 = wa (A + 4 * K) -> getr regs 12 = wa U -> getr regs 19 = wa (Z.of_nat N) ->
  getr regs 21 = wa SZ -> 1 <= A -> A + 4 * K <= 2^47 -> Z.of_nat N <= K -> 0 <= U -> U + Z.of_nat N * SZ <= 2^36 ->
  16 <= SZ <= 65536 -> wr m (A + 4 * (K - Z.of_nat N)) (4 * Z.of_nat N) ->
  exists R m', msteps SEGS (mkst regs (wa 0x449fc) m rom) (mkst R (wa 0x44a1c) m' rom) /\ getr R 10 = wa (Z.of_nat N) /\
    getr R 12 = wa (U + Z.of_nat N * SZ) /\
    (forall k, In k KPFL -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    (forall i, 0 <= i < Z.of_nat N -> rd m' (A + 4 * (K - 1 - i)) 4 ((U + i * SZ) / 16)) /\
    (forall x, 0 <= x < 2^64 -> ~ (A + 4 * (K - Z.of_nat N) <= x < A + 4 * K) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof.
  intros fx rom N regs m A K U SZ HN H10 H11 H12 H19 H21 HA HAK HNK HU HUS HSZ HWR.
  destruct (pfl_gen rom N regs m 0 (A + 4 * K) U (Z.of_nat N) SZ HN ltac:(lia) H10 H11 H12 H19 H21 ltac:(lia) ltac:(lia) HU HUS HSZ
              ltac:(replace (A + 4 * K - 4 * Z.of_nat N) with (A + 4 * (K - Z.of_nat N)) by ring; exact HWR))
    as (R & m' & Hms & B10 & B12 & KK & RD & FR & G).
  exists R, m'. split; [exact Hms|]. split; [exact B10|]. split; [exact B12|]. split; [exact KK|].
  split.
  - intros i Hi. replace (A + 4 * (K - 1 - i)) with (A + 4 * K - 4 * (0 + i + 1)) by ring. apply RD; lia.
  - split; [|exact G]. intros x Hx Hn. apply FR; [exact Hx | lia].
Qed.
End AXG_pfl.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Ltac lenq := rewrite ?length_N_to_le_bytes; change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.
Ltac znq := change (Z.of_nat 4) with 4 in *; change (Z.of_nat 8) with 8 in *.

Definition KNGL : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
Lemma ngl_loop : forall {fx : FPState} rom (k : nat) regs m FP CP (w : Z -> Z),
  (1 <= k)%nat -> getr regs 11 = wa (CP + 4 * Z.of_nat k) -> getr regs 13 = wa CP -> getr regs 20 = wa FP ->
  1 <= FP -> FP + 4 * Z.of_nat k <= 2^47 -> 1 <= CP -> CP + 4 * Z.of_nat k <= 2^47 ->
  (FP + 4 * Z.of_nat k <= CP \/ CP + 4 * Z.of_nat k <= FP) ->
  (forall i, 0 <= i < Z.of_nat k -> 0 <= w i < 2^31 /\ rd m (FP + 4 * i) 4 (w i)) ->
  wr m CP (4 * Z.of_nat k) ->
  exists R m', msteps SEGS (mkst regs (wa 0x446ac) m rom) (mkst R (wa 0x446c0) m' rom) /\
    getr R 13 = wa (CP + 4 * Z.of_nat k) /\ getr R 20 = wa (FP + 4 * Z.of_nat k) /\
    (forall kk, In kk KNGL -> getr R (Z_to_bv 5 (Z.of_nat kk)) = getr regs (Z_to_bv 5 (Z.of_nat kk))) /\
    (forall i, 0 <= i < Z.of_nat k -> rd m' (CP + 4 * i) 4 (w i)) /\
    (forall x, 0 <= x < 2^64 -> ~ (CP <= x < CP + 4 * Z.of_nat k) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof.
  intros fx rom k. induction k as [|k IH]; intros regs m FP CP w Hk H11 H13 H20 HF1 HF2 HC1 HC2 HD HW HWR; [lia|].
  rewrite Nat2Z.inj_succ in *.
  destruct (HW 0 ltac:(lia)) as [Hw0 Hr0]. rewrite Z.add_0_r in Hr0.
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXF_nglz.ngl_pre regs m FP CP (CP + 4 * Z.succ (Z.of_nat k)) (w 0)).
  { constructor; try assumption; try lia.
    - unfold rd in Hr0. rewrite Z.add_0_r. exact Hr0.
    - intros d kk Hd Hkk. rewrite Z.add_0_r. apply HWR; lia. }
  set (m1 := wbytes m (wa (CP + 0)) (word_to_le_bytes 4 (wa (ext_Z true 0 4 (w 0))))).
  assert (Hm1 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXF_nglz.ngl_mem_pnglc m regs FP CP (CP + 4 * Z.succ (Z.of_nat k)) (w 0) = m1) by reflexivity.
  assert (E1 : forall x, 0 <= x < 2^64 -> ~ (CP <= x < CP + 4) -> m1 (wa x) = m (wa x)).
  { intros x Hx Hn. unfold m1. apply wb_other; [exact Hx | lia | lenq; lia | lenq; lia]. }
  assert (R1 : rd m1 CP 4 (w 0)).
  { unfold m1. rewrite ext_Z_lo32_small by lia. rewrite Z.add_0_r. apply wb_rd_hit; lia. }
  assert (G1 : mem_grows m m1) by (unfold m1; apply wbytes_grows).
  destruct k as [|k'].
  - (* [comment removed for export] *)
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXF_nglz.ngl_pnglx regs m rom FP CP (CP + 4 * Z.succ (Z.of_nat 0)) (w 0) P
                (sc_nglx regs m FP CP (CP + 4 * Z.succ (Z.of_nat 0)) (w 0) ltac:(cbn in *; lia) ltac:(cbn; lia)))
      as (R & Hms & A11 & A12 & A13 & A20 & KK).
    assert (Hm1x : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXF_nglz.ngl_mem_pnglx m regs FP CP (CP + 4 * Z.succ (Z.of_nat 0)) (w 0) = m1) by reflexivity.
    rewrite Hm1x in Hms. exists R, m1. split; [exact Hms|]. cbn [Z.of_nat] in *.
    split; [rewrite A13; f_equal; lia|]. split; [rewrite A20; f_equal; lia|].
    split; [intros kk Hkk; apply KK; exact Hkk|].
    split; [intros i Hi; replace i with 0 by lia; rewrite Z.add_0_r; exact R1|].
    split; [intros x Hx Hn; apply E1; [exact Hx | lia] | exact G1].
  - (* [comment removed for export] *)
    destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np.AXF_nglz.ngl_pnglc regs m rom FP CP (CP + 4 * Z.succ (Z.of_nat (S k'))) (w 0) P
                (sc_nglc regs m FP CP (CP + 4 * Z.succ (Z.of_nat (S k'))) (w 0) ltac:(lia) ltac:(lia)))
      as (R & Hms & A11 & A12 & A13 & A20 & KK).
    rewrite Hm1 in Hms.
    destruct (IH R m1 (FP + 4) (CP + 4) (fun i => w (i + 1)) ltac:(lia)
                ltac:(rewrite A11; f_equal; lia) A13 A20 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R' & m' & Hms' & B13 & B20 & KK' & RD & FR & G').
    { intros i Hi. destruct (HW (i + 1) ltac:(lia)) as [Hwi Hri]. split; [exact Hwi|].
      apply (rd_frame m m1); [lia | cbn; lia | | replace (FP + 4 * (i + 1)) with (FP + 4 + 4 * i) in Hri by ring; exact Hri].
      intros x Hx. znq. apply E1; lia. }
    { intros d kk Hd Hkk. apply (store_ok_mono SEGS kk m m1 _ G1). replace (CP + 4 + d) with (CP + (4 + d)) by ring. apply HWR; lia. }
    exists R', m'. split; [exact (msteps_trans SEGS _ _ _ Hms Hms')|].
    split; [rewrite B13; f_equal; lia|]. split; [rewrite B20; f_equal; lia|].
    split; [intros kk Hkk; rewrite (KK' kk Hkk); apply KK; exact Hkk|].
    split.
    + intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
      * rewrite Z.add_0_r. apply (rd_frame m1 m'); [lia | cbn; lia | | exact R1]. intros x Hx. znq. apply FR; lia.
      * replace (CP + 4 * i) with (CP + 4 + 4 * (i - 1)) by ring. replace (w i) with (w (i - 1 + 1)) by (f_equal; ring). apply RD; lia.
    + split; [intros x Hx Hn; rewrite FR by lia; apply E1; lia | exact (mem_grows_trans _ _ _ G1 G')].
Qed.

(* [comment removed for export] *)
Section INVSTEP.
Variables (m m' : word -> option byte) (CA SB c sz nc newc j SP : Z).
Hypothesis I : INV_C m CA SB c sz nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA + 2592 <= SP - 2048.
Hypothesis HSB : 4194304 <= SB /\ SB + 137438953472 + 4096 <= SP - 2048 /\ SP <= 2^47.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis G : mem_grows m m'.

Ltac frm FR := apply (rd_frame m m'); [slia | znq; slia | intros x Hx; znq; apply FR; unfold owned_C; slia | ].

#[using="I Hj HCA HSB HSEP G"] Lemma inv_pop : 1 <= cnt_of nc j ->
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (REC CA c <= x < REC CA c + 4) -> ~ (CA + 2576 <= x < CA + 2584) -> m' (wa x) = m (wa x)) ->
  rd m' (REC CA c) 4 (cnt_of nc j - 1) -> (exists st, 0 <= st < 2^64 /\ rd m' (CA + 2576) 8 st) ->
  INV_C m' CA SB c sz nc newc (j + 1).
Proof. LiaFast.lf_pins (fun (I Hj HCA HSB HSEP G : LiaFast.U) => LiaFast.u0).
  intros Hc FR Rc Rst. destruct I as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  destruct (pop_step nc j ltac:(slia) ltac:(slia) Hc) as [Eb Ec].
  pose proof (b_of_pos nc j ltac:(slia) ltac:(slia)) as Hb. pose proof (b_of_bounds nc j ltac:(slia) ltac:(slia)) as Hbb.
  pose proof (cnt_of_range nc j ltac:(slia) ltac:(slia)) as Hcr.
  constructor.
  - slia.
  - frm FR. exact ISB.
  - frm FR. exact IRIB.
  - rewrite Ec. exact Rc.
  - frm FR. exact Imc.
  - frm FR. exact Isz.
  - intros i Hi. rewrite Ec in Hi |- *. replace (j + 1 + (cnt_of nc j - 1) - 1 - i) with (j + cnt_of nc j - 1 - i) by ring.
    frm FR. apply Ich. slia.
  - frm FR. exact Imu.
  - rewrite Eb. frm FR. exact Inf.
  - destruct Ina as (na & Hna & Rna). exists na. split; [exact Hna|]. frm FR. exact Rna.
  - intros k Hk. rewrite Eb in Hk. assert (Hnb : nc * b_of nc j <= newc) by slia.
    frm FR. apply Ifa. exact Hk.
  - exact Rst.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwrec; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwri; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwst; assumption.
Qed.

#[using="I Hj HCA HSB HSEP G"] Lemma inv_refill : cnt_of nc j = 0 ->
  (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) ->
  rd m' (REC CA c) 4 (nc - 1) -> rd m' (REC CA c + 4) 4 (2 * nc) -> rd m' (REC CA c + 8) 8 sz ->
  (forall i, 0 <= i < nc -> rd m' (REC CA c + 16 + 4 * i) 4 ((j + nc - 1 - i) * (sz / 16))) ->
  rd m' (RIX SB c) 8 0 -> rd m' (RIX SB c + 16) 8 (newc - nc * b_of nc j - nc) ->
  (exists na, 0 <= na < 2^64 /\ rd m' (RIX SB c + 72) 8 na) ->
  (exists st, 0 <= st < 2^64 /\ rd m' (CA + 2576) 8 st) ->
  INV_C m' CA SB c sz nc newc (j + 1).
Proof. LiaFast.lf_pins (fun (I Hj HCA HSB HSEP G : LiaFast.U) => LiaFast.u0).
  intros Hc FR Rc Rmc Rsz Rch Rmu Rnf Rna Rst. destruct I as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  destruct (refill_step nc j ltac:(slia) ltac:(slia) Hc) as (Ej & Eb & Ec).
  pose proof (b_of_pos nc j ltac:(slia) ltac:(slia)) as Hb.
  constructor.
  - slia.
  - frm FR. exact ISB.
  - frm FR. exact IRIB.
  - rewrite Ec. exact Rc.
  - exact Rmc.
  - exact Rsz.
  - intros i Hi. rewrite Ec in Hi |- *. replace (j + 1 + (nc - 1) - 1 - i) with (j + nc - 1 - i) by ring. apply Rch. slia.
  - exact Rmu.
  - rewrite Eb. replace (newc - nc * (b_of nc j + 1)) with (newc - nc * b_of nc j - nc) by ring. exact Rnf.
  - exact Rna.
  - intros k Hk. rewrite Eb in Hk. assert (Hnb : nc * b_of nc j <= newc) by slia.
    frm FR. apply Ifa. slia.
  - exact Rst.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwrec; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwri; assumption.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m m' _ G). apply Iwst; assumption.
Qed.
End INVSTEP.
