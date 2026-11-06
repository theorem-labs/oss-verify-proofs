(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import MemsetLib AsanMemset_code AsanMemset1 AsanMemset.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fs5_consts : fs_N 5 = 512 /\ fs_flo 5 = 35840 /\ fs_fro 5 = 5279744 /\ fs_fsz 5 = 2048.
Proof. repeat split; reflexivity. Qed.

Lemma fs_flag5 : forall FS p, fs_flag FS 5 p = FS + 35840 + p.
Proof. intros. unfold fs_flag. pose proof fs5_consts as (_ & -> & _). reflexivity. Qed.
Lemma fs_frame5 : forall FS p, fs_frame FS 5 p = FS + 5279744 + p * 2048.
Proof. intros. unfold fs_frame. pose proof fs5_consts as (_ & _ & -> & ->). reflexivity. Qed.
Lemma fs_hint5 : forall FS, fs_hint FS 5 = FS + 40.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_clear_low : forall a k, 0 <= a < 2 ^ 64 -> 0 < k < 64 ->
  Z.land a (2 ^ 64 - 2 ^ k) = 2 ^ k * (a / 2 ^ k).
Proof.
  intros a k Ha Hk.
  assert (Hmask : 2 ^ 64 - 2 ^ k = Z.shiftl (Z.ones (64 - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. unfold Z.ones. rewrite Z.shiftl_1_l.
    replace (2 ^ 64) with (2 ^ (64 - k) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia. }
  rewrite Hmask. rewrite <- Z.shiftr_div_pow2, Z.mul_comm, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i k) as [L|Ge].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. replace (i - k + k) with i by lia.
    rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec (i - k) (64 - k)).
    + apply andb_true_r.
    + rewrite andb_false_r. destruct (Z.eq_dec a 0) as [->|NE]; [rewrite Z.bits_0; reflexivity|].
      rewrite Z.bits_above_log2; [reflexivity|lia|]. assert (Z.log2 a < 64) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma land_align32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x ((-32) mod 2 ^ 64) = 32 * (x / 32).
Proof.
  intros x Hx. change ((-32) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 5). rewrite land_clear_low by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mscells (m : word -> option byte) : Prop :=
  cellN SEGS_A m 0x129ec8 8 0x12be88 /\ cellN SEGS_A m 0x12be88 8 0x11cfa4.
(* [comment removed for export] *)
Definition suar (m : word -> option byte) : Prop :=
  cellN SEGS_A m 0x129f00 8 0x132280 /\ cellN SEGS_A m 0x132280 4 1.

Lemma mscells_intro : forall m, ro_ok SEGS_A RO_A m -> mscells m.
Proof.
  intros m RO. split; (eapply cellN_ro_A; [exact RO | vm_compute; reflexivity | vm_compute; reflexivity | lia | cbn; lia]).
Qed.
Lemma suar_intro : forall m, rt_ok m -> ro_ok SEGS_A RO_A m -> suar m.
Proof.
  intros m RT RO. split.
  - eapply cellN_ro_A; [exact RO | vm_compute; reflexivity | vm_compute; reflexivity | lia | cbn; lia].
  - eapply cellN_rt_A; [exact RT | vm_compute; reflexivity | lia | cbn; lia].
Qed.
Lemma shcells_intro : forall m, rt_ok m -> ro_ok SEGS_A RO_A m -> shcells m.
Proof.
  intros m RT RO. split.
  - eapply cellN_ro_A; [exact RO | vm_compute; reflexivity | vm_compute; reflexivity | lia | cbn; lia].
  - eapply cellN_rt_A; [exact RT | vm_compute; reflexivity | lia | cbn; lia].
Qed.
Lemma tblsh_intro : forall m, gsh_ok m -> tblsh m.
Proof.
  intros m G g Hg. eapply cellN_byte; [| lia | lia | lia].
  eapply mem_byte_of_tbl; [exact G|].
  assert (C : g = 0 \/ g = 1 \/ g = 2 \/ g = 3 \/ g = 4 \/ g = 5) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> | ->]]]]]; vm_compute; reflexivity.
Qed.
Lemma five_tbl_A0 : arr32 SEGS_A (fun _ => None) 145344 five_tbl.
Proof.
  intros i Hi. cbn [length five_tbl] in Hi.
  assert (H : forallb (fun k => match rdn SEGS_A (fun _ => None) (Z_to_bv 64 (145344 + 4 * Z.of_nat k)) 4 with
                               | Some bs => bytes_le_to_Z bs =? nth k five_tbl 0 | None => false end) (seq 0 12) = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H i ltac:(apply in_seq; lia)) as Hk. cbn beta in Hk. unfold cellN.
  destruct (rdn SEGS_A _ _ 4) as [bs|]; [|discriminate]. exists bs. split; [reflexivity|]. apply Z.eqb_eq. exact Hk.
Qed.
Lemma five_tbl_intro : forall m, ro_ok SEGS_A RO_A m -> arr32 SEGS_A m 145344 five_tbl.
Proof.
  intros m RO. eapply BnCbdLib.arr32_rom; [lia | cbn; lia | | apply five_tbl_A0].
  intros x b Hx Hb. apply RO; [|exact Hb]. cbn [length five_tbl] in Hx. exists (0x10000, 0x4e000). split; [left; reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
Definition highr (r : Z * Z) : Prop :=
  2 ^ 32 <= fst r \/ (IMG <= fst r /\ snd r <= LOSH) \/ (LSLO <= fst r /\ snd r <= LSHI).

(* [comment removed for export] *)
Lemma cellN_low_unch : forall m m' rs a n v,
  unch m m' rs -> (forall r, In r rs -> highr r) -> 0 <= a -> (a + Z.of_nat n <= IMG \/ (SHA <= a /\ a + Z.of_nat n <= LSLO)) ->
  cellN SEGS_A m a n v -> cellN SEGS_A m' a n v.
Proof.
  intros m m' rs a n v U H Ha Hb C. eapply cellN_unch; [exact U | lia | lia | | exact C].
  intros r Hr. specialize (H r Hr). unfold highr in H. lia.
Qed.
Lemma mscells_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> mscells m -> mscells m'.
Proof. intros m m' rs U H [A B]. split; (eapply cellN_low_unch; [exact U | exact H | lia | cbn; lia | assumption]). Qed.
Lemma suar_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> suar m -> suar m'.
Proof. intros m m' rs U H [A B]. split; (eapply cellN_low_unch; [exact U | exact H | lia | cbn; lia | assumption]). Qed.
Lemma shcells_unch' : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> shcells m -> shcells m'.
Proof. intros m m' rs U H [A B]. split; (eapply cellN_low_unch; [exact U | exact H | lia | cbn; lia | assumption]). Qed.
Lemma tblsh_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> tblsh m -> tblsh m'.
Proof. intros m m' rs U H T g Hg. eapply cellN_low_unch; [exact U | exact H | lia | cbn; lia | apply T; exact Hg]. Qed.
Lemma five_tbl_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) ->
  arr32 SEGS_A m 145344 five_tbl -> arr32 SEGS_A m' 145344 five_tbl.
Proof.
  intros m m' rs U H T. eapply arr32_unch; [exact U | lia | cbn; lia | | exact T].
  intros r Hr. specialize (H r Hr). unfold highr in H. cbn [length five_tbl]. lia.
Qed.
Lemma rt_ok_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> rt_ok m -> rt_ok m'.
Proof.
  intros m m' rs U H RT a b Hin. specialize (RT a b Hin). destruct RT as (bs & Hr & Hv). exists bs. split; [|exact Hv].
  assert (Ha : 0 <= a < IMG).   (* [comment removed for export] *)
  { pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun c => (0 <=? fst c) && (fst c <? IMG)) RT_A = true) (a, b) Hin) as X.
    cbn [fst] in X. lia. }
  rewrite <- Hr. cbn [rdn]. rewrite (U (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hr1 & Hr2). specialize (H r Hr1). unfold highr in H. rewrite u_Z2bv64, Z.mod_small in Hr2 by lia. lia.
Qed.
Lemma ro_ok_unchA : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> ro_ok SEGS_A RO_A m -> ro_ok SEGS_A RO_A m'.
Proof.
  intros m m' rs U H RO. eapply ro_ok_unch; [exact U | | exact RO].
  intros a (r0 & Hin & Hr0). assert (X : 0 <= a < IMG).   (* [comment removed for export] *)
  { pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun c => (0 <=? fst c) && (snd c <? IMG)) RO_A = true) r0 Hin) as Y.
    cbn beta in Y. apply andb_true_iff in Y. destruct Y as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. lia. }
  split; [lia|]. intros r Hr. specialize (H r Hr). unfold highr in H. lia.
Qed.
Lemma gsh_ok_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> highr r) -> gsh_ok m -> gsh_ok m'.
Proof.
  intros m m' rs U H G. eapply cells_ok_unch; [exact U | | exact G].
  intros a b Hin.
  assert (Ha : SHA <= a < LSLO).   (* [comment removed for export] *)
  { pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun c => (SHA <=? fst c) && (fst c <? LSLO)) GSH_A = true) (a, b) Hin) as X.
    cbn [fst] in X. lia. }
  split; [lia|]. intros r Hr. specialize (H r Hr). unfold highr in H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unch_of_frame : forall m m' rs, mem_frame m m' rs -> unch m m' rs.
Proof. intros m m' rs [A _] x Hx. apply A. exact Hx. Qed.
Lemma grows_of_frame : forall m m' rs, mem_frame m m' rs -> mem_grows m m'.
Proof.
  intros m m' rs [_ B] x Hx. destruct (m x) as [b|] eqn:E; [|congruence].
  destruct (B x b E) as [b' Hb']. rewrite Hb'. discriminate.
Qed.
Lemma keeps_of_cs : forall regs regs', keeps_cs regs regs' -> keeps CS regs regs'.
Proof. intros regs regs' K r Hr. apply K. exact Hr. Qed.
(* [comment removed for export] *)
Lemma unch_store_bs : forall m a (bs : list byte) rs lo hi,
  0 <= a -> a + Z.of_nat (length bs) <= M64 -> In (lo, hi) rs -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
  unch m (wbytes m (Z_to_bv 64 a) bs) rs.
Proof.
  intros m a bs rs lo hi Ha Hb Hin Hlo Hhi x Hx.
  destruct bs as [|b0 bs']; [reflexivity|].
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite u_Z2bv64; apply Z.mod_small; cbn [length] in Hb; zwidth; lia).
  assert (Hout : ~ (a <= bv_unsigned x < a + Z.of_nat (length (b0 :: bs')))).
  { intros Hc. apply Hx. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. lia. }
  destruct (Z.lt_ge_cases (bv_unsigned x) a).
  - apply wbytes_below; rewrite ?Hu; cbn [length] in *; lia.
  - apply wbytes_above. rewrite Hu. lia.
Qed.

(* [comment removed for export] *)
Lemma malloc_ctx_ok_unch : forall wlo whi wlo' whi' FS m m' rs,
  malloc_ctx_ok wlo whi FS m -> unch m m' rs -> mem_grows m m' ->
  (forall r, In r rs -> IMG <= fst r /\ ((wlo <= fst r /\ snd r <= whi) \/ (FS <= fst r /\ snd r <= FS + FS_LEN) \/ (LOSH <= fst r /\ snd r <= KHI_A))) ->
     (* [comment removed for export] *)
  wlo <= wlo' -> whi' <= whi -> malloc_ctx_ok wlo' whi' FS m'.
Proof.
  intros wlo whi wlo' whi' FS m m' rs (CTX & THR & DT & H1 & H2 & H3 & H4 & H5 & B1 & B2 & B3 & B4 & C1 & C2 & C3) U Gr HR Hlo Hhi.
  unfold ctx_cell_ok, app_mem, KHI_A, HIEND_A, IMGHI_A, LOSH_A, FS_LEN in *.
  exists CTX, THR, DT. unfold ctx_cell_ok, app_mem, KHI_A, HIEND_A, IMGHI_A, LOSH_A, FS_LEN.
  split; [eapply cellN_unch; [exact U | lia | cbn; lia | intros r Hr; destruct (HR r Hr) as [X _]; cbn; lia | exact H1]|].   (* [comment removed for export] *)
  split.
  { eapply mem_u64_unch; [exact U | lia | lia | | exact H2]. intros r Hr. destruct (HR r Hr) as [_ X]. cbn. lia. }
  split; [eapply mem_def_grows; [exact Gr | exact H3]|].
  split; [eapply cellN_unch; [exact U | lia | cbn; lia | intros r Hr; destruct (HR r Hr) as [X _]; cbn; lia | exact H4]|].
  split.
  { eapply mem_u64_unch; [exact U | lia | unfold TP_A in *; lia | | exact H5]. intros r Hr. destruct (HR r Hr) as [_ X]. cbn. lia. }
  repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SETSH_KEEP : list Z := [1; 2; 3; 4; 5; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

#[using="Type"] Lemma setsh_A : forall (f8 : bool) regs m (a n : Z) (ret : word),
  getr regs 10%bv = Z_to_bv 64 a -> getr regs 11%bv = Z_to_bv 64 n -> getr regs 1%bv = ret -> ret_ok ret ->
  0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 a) (Z.to_nat n) = true -> mscells m ->
  exists regs',
    msteps SEGS_A (mkst regs (Z_to_bv 64 (if f8 then 0x7844c else 0x7832c)) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 a) (repeat (Z_to_bv 8 (if f8 then 248 else 0)) (Z.to_nat n))) rom)
    /\ keeps SETSH_KEEP regs regs'.
Proof.
  intros f8 regs m a n ret R10 R11 R1 Hret Ha Hn Han Hst [MC1 MC2].
  pose proof (u64_range ret) as Hr.
  replace (1%bv : reg) with (Z_to_bv 5 1 : reg) in R1 by (apply bv_eq; reflexivity).
  assert (STUB : forall pc cvz, (pc = 0x7844c /\ cvz = 248) \/ (pc = 0x7832c /\ cvz = 0) ->
    exists regs1, msteps SEGS_A (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs1 (Z_to_bv 64 0x11cfa4) m rom)
      /\ getr regs1 10%bv = Z_to_bv 64 a /\ getr regs1 11%bv = Z_to_bv 64 cvz /\ getr regs1 12%bv = Z_to_bv 64 n
      /\ getr regs1 1%bv = ret /\ keeps SETSH_KEEP regs regs1).
  { intros pc cvz [[-> ->]|[-> ->]].
    - zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                            [KC (ZL 0) 0x129ec8 8 (ZL 0x12be88); KC (ZL 0) 0x12be88 8 (ZL 0x11cfa4)] (@nil kwin))
        10%nat [0x11cfa4] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33)]) [a; n]
        constr:([Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs m rom 0x7844c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 MC1; kc1 MC2; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
      exists regs1. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (1%bv : reg) ZR ltac:(vm_compute; reflexivity)) | rewrite <- R1; reflexivity]|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
    - zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                            [KC (ZL 0) 0x129ec8 8 (ZL 0x12be88); KC (ZL 0) 0x12be88 8 (ZL 0x11cfa4)] (@nil kwin))
        10%nat [0x11cfa4] (SCR [] []) constr:([(10%bv : reg, ZV 32); (11%bv : reg, ZV 33)]) [a; n]
        constr:([Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs m rom 0x7832c.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 MC1; kc1 MC2; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
      exists regs1. split; [exact ZM|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [etransitivity; [exact (reg_kept _ _ _ _ (1%bv : reg) ZR ltac:(vm_compute; reflexivity)) | rewrite <- R1; reflexivity]|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
  destruct (STUB (if f8 then 0x7844c else 0x7832c) (if f8 then 248 else 0)) as (regs1 & M1 & A10 & A11 & A12 & A1 & K1);
    [destruct f8; [left|right]; split; reflexivity|].
  destruct (memset_summary m (Z_to_bv 64 a) (Z_to_bv 64 (if f8 then 248 else 0)) ret n rom Hn
              ltac:(rewrite u_Z2bv64, Z.mod_small by lia; lia) Hst Hret regs1 A10 A11 A12 A1) as (regs2 & M2 & B10 & AG).
  exists regs2. split.
  - eapply msteps_trans; [exact M1|]. unfold cbyte in M2. rewrite u_Z2bv64, Z.mod_small in M2 by (destruct f8; lia). exact M2.
  - intros r Hrr. etransitivity; [| exact (K1 r Hrr)]. apply (ms_agree_getr _ _ _ AG).
    cbn in Hrr. unfold ms_clob. cbn [In].
    decompose [or] Hrr; subst; intros HH; decompose [or] HH; try discriminate; auto.
Qed.
End S.
