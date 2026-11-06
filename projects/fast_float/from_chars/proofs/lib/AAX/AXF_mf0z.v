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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Module AXF_mf0.
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

Definition e_AD := EVar 32.
Definition e_SZ := EVar 33.
Definition e_NM := EVar 34.
Definition e_CF := EVar 35.
Definition STK := SA (EVar 2) (-1024).
Definition sr_mf0 := (sr_upd (sr_upd (sr_upd sr_id 11 (e_AD)) 12 (e_SZ)) 13 (e_NM)).
Definition kn_mf0 : list kentry :=
  [ KRange e_AD 4096 (2^47);
    KAlign e_AD 4096;
    KRange e_SZ 4096 (2^32);
    KAlign e_SZ 4096;
    KRange e_NM 1 (2^47);
    KRange e_CF 1 (2^47);
    KRange (EVar 2) (2^46) (2^47);
    KWord (SA (ELit 0) 904176) 8 (ELit 1525856);
    KWord (SA (ELit 0) 1525856) 8 (ELit 4096);
    KWord (SA (ELit 0) 904192) 8 e_CF;
    KWord (SA e_CF 260) 1 (ELit 0);
    KWr STK (ELit 1024) ].
Definition scr_mf0 : scripts := SCR [] [] [].
Definition ss_mf0 := SS 0x7db90 sr_mf0 [] kn_mf0 36.
Definition RUN_mf0 := sym_exec SEGS 120 true [0x73c44] scr_mf0 ss_mf0 [].

Definition scr_pmf0 : scripts := SCR [] [] [].
Definition RES_pmf0 := Eval vm_compute in sym_exec SEGS 120 true [0x73c44] scr_pmf0 ss_mf0 [].
Lemma RES_pmf0_ok : sym_exec SEGS 120 true [0x73c44] scr_pmf0 (SS 0x7db90 sr_mf0 [] kn_mf0 36) [] = RES_pmf0.
Proof. vm_compute. reflexivity. Qed.
End AXF_mf0.


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section MF0.
Context {fx : FPState}.

Definition VALS_mf0 (AD SZ NM CF : Z) : list Z := [AD; SZ; NM; CF].

Record mf0_pre (regs : bvmap 5 word) (m : word -> option byte) (AD SZ NM CF : Z) : Prop := {
  mf0_R11 : getr regs 11 = wa AD ;
  mf0_R12 : getr regs 12 = wa SZ ;
  mf0_R13 : getr regs 13 = wa NM ;
  mf0_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  mf0_rng_AD : 4096 <= AD <= 2^47 ;
  mf0_rng_SZ : 4096 <= SZ <= 2^32 ;
  mf0_rng_NM : 1 <= NM <= 2^47 ;
  mf0_rng_CF : 1 <= CF <= 2^47 ;
  mf0_ka1 : AD mod 4096 = 0 ;
  mf0_ka3 : SZ mod 4096 = 0 ;
  mf0_kr6 : (2^46) <= bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) <= (2^47) ;
  mf0_kw7 : rdn SEGS m (wa (0 + 904176)) 8 = Some (word_to_le_bytes 8 (wa 1525856)) ;
  mf0_kw8 : rdn SEGS m (wa (0 + 1525856)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mf0_kw9 : rdn SEGS m (wa (0 + 904192)) 8 = Some (word_to_le_bytes 8 (wa CF)) ;
  mf0_kw10 : rdn SEGS m (wa (CF + 260)) 1 = Some (word_to_le_bytes 1 (wa 0))
}.


#[using="Type"] Lemma mf0_setup : forall regs m AD SZ NM CF, mf0_pre regs m AD SZ NM CF ->
  regs_ok (Ez regs (VALS_mf0 AD SZ NM CF)) AXF_mf0.sr_mf0 regs /\ know_ok SEGS (Ez regs (VALS_mf0 AD SZ NM CF)) m AXF_mf0.kn_mf0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m AD SZ NM CF P. destruct P as [mf0_R11 mf0_R12 mf0_R13 mf0_HSTK mf0_rng_AD mf0_rng_SZ mf0_rng_NM mf0_rng_CF mf0_ka1 mf0_ka3 mf0_kr6 mf0_kw7 mf0_kw8 mf0_kw9 mf0_kw10].
  set (E := Ez regs (VALS_mf0 AD SZ NM CF)).
  assert (Z32 : bv_unsigned (ev E 32) = AD) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = NM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = CF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  split.
  { unfold AXF_mf0.sr_mf0.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite mf0_R11. reflexivity.
    - rewrite mf0_R12. reflexivity.
    - rewrite mf0_R13. reflexivity. }
  unfold know_ok, AXF_mf0.kn_mf0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m (EVar 2) (getr regs 2) 1024); [reflexivity | assumption | first [lia | (replace (getr regs 2) with (getr regs (Z_to_bv 5 (Z.of_nat 2))) by (f_equal; apply bv_eq; reflexivity); lia)]])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_mf0.e_AD AXF_mf0.e_SZ AXF_mf0.e_NM AXF_mf0.e_CF AXF_mf0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z2.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range AD _ _ mf0_rng_AD eq_refl eq_refl), ?(mod64_of_range SZ _ _ mf0_rng_SZ eq_refl eq_refl), ?(mod64_of_range NM _ _ mf0_rng_NM eq_refl eq_refl), ?(mod64_of_range CF _ _ mf0_rng_CF eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mf0_rng_AD mf0_rng_SZ mf0_rng_NM mf0_rng_CF mf0_ka1 mf0_ka3 mf0_kr6; lia).
  all: first [lia].
Qed.


Definition mf0_mem_pmf0 (m : word -> option byte) (regs : bvmap 5 word) (AD SZ NM CF : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -40)) (word_to_le_bytes 8 (wa 515004))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -48)) (word_to_le_bytes 8 (wa SZ))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -56)) (word_to_le_bytes 8 (wa AD))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128)) (word_to_le_bytes 4 (wa 50))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -136)) (word_to_le_bytes 8 (wa 481768))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -144)) (word_to_le_bytes 8 (wa SZ))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -152)) (word_to_le_bytes 8 (wa 1))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -160)) (word_to_le_bytes 8 (wa AD))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -168)) (word_to_le_bytes 8 (wa NM))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -176)) (word_to_le_bytes 8 (wa 1525856))) (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -184)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))))).

#[using="Type"] Theorem mf0_pmf0 : forall regs m rom AD SZ NM CF, mf0_pre regs m AD SZ NM CF ->
  scs_denot SEGS m (Ez regs (VALS_mf0 AD SZ NM CF)) (snd (fst AXF_mf0.RES_pmf0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x7db90) m rom) (mkst R (wa 0x73c44) (mf0_mem_pmf0 m regs AD SZ NM CF) rom) /\
    getr R 1 = wa 481796 /\ getr R 2 = wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) + -128) /\ getr R 8 = wa SZ /\ getr R 9 = wa 1 /\ getr R 10 = wa AD /\ getr R 11 = wa SZ /\ getr R 12 = wa 3 /\ getr R 13 = wa 50 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 17 = wa 222 /\ getr R 18 = wa AD /\ getr R 19 = wa NM /\ getr R 20 = wa 1525856 /\ (forall k, In k [3; 4; 5; 6; 7; 16; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom AD SZ NM CF P Hsc. destruct (mf0_setup regs m AD SZ NM CF P) as [HR HK].
  set (E := Ez regs (VALS_mf0 AD SZ NM CF)) in *. destruct P as [mf0_R11 mf0_R12 mf0_R13 mf0_HSTK mf0_rng_AD mf0_rng_SZ mf0_rng_NM mf0_rng_CF mf0_ka1 mf0_ka3 mf0_kr6 mf0_kw7 mf0_kw8 mf0_kw9 mf0_kw10].
  assert (Z32 : bv_unsigned (ev E 32) = AD) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = SZ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = NM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = CF) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z2 : bv_unsigned (ev E 2) = bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2)))) by reflexivity.

  destruct (run_sound SEGS 120 [0x73c44] AXF_mf0.scr_pmf0 0x7db90 AXF_mf0.sr_mf0 AXF_mf0.kn_mf0 36 _ _ _ E m rom regs AXF_mf0.RES_pmf0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mf0.RES_pmf0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mf0_mem_pmf0 m regs AD SZ NM CF) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mf0_mem_pmf0. repeat (apply (f_equal3 wbytes)); try reflexivity.
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
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MF0.
