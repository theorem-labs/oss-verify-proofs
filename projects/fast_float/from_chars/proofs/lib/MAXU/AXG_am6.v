(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_am1 AXG_am5.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt3wz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mmwrz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mmrrz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt8xz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mpwz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt6z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am5.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac klist H := first [ AxSymRun3.klist_refl H | (cbn [In] in H |- *; repeat (destruct H as [<-|H]; [first [solve [memb] | (exfalso; congruence)] |]); destruct H) ].      (* [comment removed for export] *)
Ltac regk KK k := match goal with |- getr _ ?r0 = _ => replace r0 with (Z_to_bv 5 (Z.of_nat k)) by (apply bv_eq; reflexivity) end;
  rewrite (KK k ltac:(cbn [In]; solve [memb])).

Section AM6.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition mmap_saves (m : word -> option byte) (spc ra v8 v9 v18 v19 v20 v21 : Z) : Prop :=
  rdn SEGS m (wa (spc + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) /\
  rdn SEGS m (wa (spc + -16)) 8 = Some (word_to_le_bytes 8 (wa v8)) /\
  rdn SEGS m (wa (spc + -24)) 8 = Some (word_to_le_bytes 8 (wa v9)) /\
  rdn SEGS m (wa (spc + -32)) 8 = Some (word_to_le_bytes 8 (wa v18)) /\
  rdn SEGS m (wa (spc + -40)) 8 = Some (word_to_le_bytes 8 (wa v19)) /\
  rdn SEGS m (wa (spc + -48)) 8 = Some (word_to_le_bytes 8 (wa v20)) /\
  rdn SEGS m (wa (spc + -56)) 8 = Some (word_to_le_bytes 8 (wa v21)).

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bdm : forall R m rom sp0 can ra s0 s1 s2 s3 s4 ar sh,
  am_frame R m sp0 can ra s0 s1 s2 s3 s4 -> getr R 8 = wa 4096 ->
  rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa 18446744073709551615)) ->
  0 <= ar <= 2^64-1 -> rdn SEGS m (wa (0 + 621792)) 8 = Some (word_to_le_bytes 8 (wa ar)) ->
  0 <= sh <= 34 -> rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ->
  stk_ok SEGS m (wa (sp0 + -64)) 1024 -> 2^20 + 1024 <= sp0 ->
  exists R' m', msteps SEGS (mkst R (wa 0x53b68) m rom) (mkst R' (wa 0x551a4) m' rom) /\
    getr R' 17 = wa 222 /\ getr R' 10 = wa 0 /\ getr R' 11 = wa (4096 * Z.shiftl 2 sh) /\ getr R' 12 = wa 0 /\ getr R' 13 = wa 34 /\
    getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\ getr R' 16 = wa 0 /\ getr R' 2 = wa (sp0 + -64 + -64) /\
    (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    mmap_saves m' (sp0 + -64) 343108 4096 (Z.shiftl 2 sh) 621568 621712 18446744073709551615 (bv_unsigned (getr R 21)) /\
    (forall x, 0 <= x < 2^64 -> ~ (sp0 - 128 <= x < sp0 - 64) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 can ra s0 s1 s2 s3 s4 ar sh F R8 Mac Mbk Rar Mar Rsh Msh STK Hsp.
  pose proof (mf_Rsp _ _ _ _ _ _ _ _ _ _ F) as Rsp. pose proof (mf_Asp _ _ _ _ _ _ _ _ _ _ F) as Asp.
  assert (P1 : mt3w_pre R m 0 18446744073709551615 ar sh)
    by (constructor; [exact R8 | exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | lia | lia | exact Rar | lia | exact Mac | exact Mbk | exact Mar | exact Msh]).
  destruct (mt3w_pmt3dw R m rom 0 18446744073709551615 ar sh P1) as (R1 & Hms1 & A1 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A19 & A20 & Ak1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt3w.RES_pmt3dw fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; first [rewrite br_eq_z | rewrite br_ne_z]; cbn [zeval edenot].
    all: rewrite ?(zatom R (VALS_mt3w 0 18446744073709551615 ar sh) 32 0 eq_refl eq_refl) by lia.
    all: rewrite ?(zatom R (VALS_mt3w 0 18446744073709551615 ar sh) 33 18446744073709551615 eq_refl eq_refl) by lia.
    all: reflexivity. }
  change (mt3w_mem_pmt3dw m R 0 18446744073709551615 ar sh) with m in Hms1.
  assert (R2sp : getr R1 2 = wa (sp0 + -64)) by (regk Ak1 2%nat; exact (mf_R2 _ _ _ _ _ _ _ _ _ _ F)).
  assert (P2 : mmwr_pre R1 m (sp0 + -64) 0 (4096 * Z.shiftl 2 sh) 0 34).
  { constructor; [exact R2sp | exact A10 | exact A11 | exact A12 | exact A13 | exact A14 | exact A15 | exact STK | lia | lia | | lia | lia |].
    - rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_le_mono_r 2 (sh) 34 ltac:(lia) ltac:(lia)). lia.
    - clear - Asp. apply Z.mod_divide in Asp; [|lia]. destruct Asp as (k & ->). replace (k * 16 + -64) with ((k - 4) * 16) by ring. apply Z.mod_mul. lia. }
  destruct (mmwr_pnfr R1 m rom (sp0 + -64) 0 (4096 * Z.shiftl 2 sh) 0 34 P2) as (R2 & Hms2 & B2 & B5 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & Bk2).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mmwr.RES_pnfr fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot]. rewrite (zatom R1 (VALS_mmwr (sp0 + -64) 0 (4096 * Z.shiftl 2 sh) 0 34) 36 34 eq_refl eq_refl) by lia.
    reflexivity. }
  set (m2 := mmwr_mem_pnfr m R1 (sp0 + -64) 0 (4096 * Z.shiftl 2 sh) 0 34) in *.
  exists R2, m2. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
  split; [exact B17|]. split; [exact B10|]. split; [exact B11|]. split; [exact B12|]. split; [exact B13|]. split; [exact B14|].
  split; [exact B15|]. split; [exact B16|]. split; [exact B2|].
  split.
  { intros k Hk'. rewrite (Bk2 k ltac:(clear - Hk'; klist Hk')), (Ak1 k ltac:(clear - Hk'; klist Hk')). reflexivity. }
  assert (W : forall k v, getr R1 (Z_to_bv 5 (Z.of_nat k)) = wa v -> 0 <= v < 2^64 -> bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat k))) = v).
  { intros k v E Hv. rewrite E. apply u_wa_small. exact Hv. }
  split.
  - unfold mmap_saves, m2, mmwr_mem_pnfr.
    assert (E1 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 1))) = 343108) by (apply W; [litr2 A1; reflexivity | lia]).
    assert (E8 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 8))) = 4096) by (apply W; [litr2 A8; reflexivity | lia]).
    assert (E9 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 9))) = Z.shiftl 2 sh).
    { apply W; [litr2 A9; reflexivity|]. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_le_mono_r 2 (sh) 34 ltac:(lia) ltac:(lia)). lia. }
    assert (E18 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 18))) = 621568).
    { apply W; [|lia]. rewrite (Ak1 18%nat ltac:(cbn [In]; memb)). litr2 (mf_R18 _ _ _ _ _ _ _ _ _ _ F). reflexivity. }
    assert (E19 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 19))) = 621712) by (apply W; [litr2 A19; reflexivity | lia]).
    assert (E20 : bv_unsigned (getr R1 (Z_to_bv 5 (Z.of_nat 20))) = 18446744073709551615) by (apply W; [litr2 A20; reflexivity | lia]).
    assert (E21 : getr R1 (Z_to_bv 5 (Z.of_nat 21)) = getr R (Z_to_bv 5 (Z.of_nat 21))) by (apply Ak1; cbn [In]; memb).
    rewrite E1, E8, E9, E18, E19, E20, E21.
    repeat split; repeat (rewrite rdn_wbytes_disjoint; [| side | side]); first [ (apply rdn_wbytes_hit8; side) | (rewrite wa_u; apply rdn_wbytes_hit8; side) ].
  - split.
    + intros x Hx Hn. unfold m2, mmwr_mem_pnfr. do 7 (rewrite MngWb.wbytes_out by side). reflexivity.
    + unfold m2, mmwr_mem_pnfr. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.
End AM6.

Section AM6b.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition rvx_mem (m : word -> option byte) (a sh : Z) : word -> option byte :=
  wbytes (wbytes (wbytes m (wa (0 + 621760)) (word_to_le_bytes 8 (wa (Z.shiftl 2 sh + -1))))
    (wa (0 + 621768)) (word_to_le_bytes 8 (wa (sh + 1)))) (wa (0 + 621792)) (word_to_le_bytes 8 (wa (a + 4096))).

#[using="Type"] Theorem seg_rvx : forall R m rom sp0 a sh v21,
  getr R 2 = wa (sp0 + -64 + -64) -> getr R 10 = wa a -> getr R 16 = wa 0 ->
  2^20 + 1024 <= sp0 <= 2^47 -> sp0 mod 16 = 0 -> 0 <= v21 <= 2^64-1 ->
  mmap_saves m (sp0 + -64) 343108 4096 (Z.shiftl 2 sh) 621568 621712 18446744073709551615 v21 ->
  4096 <= a <= 2^47 -> a mod 4096 = 0 -> 0 <= sh <= 34 ->
  rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (0 + 621760 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621792 + d)) k = true) ->
  exists R', msteps SEGS (mkst R (wa 0x551a8) m rom) (mkst R' (wa 0x551cc) (rvx_mem m a sh) rom) /\
    getr R' 1 = wa 343320 /\ getr R' 2 = wa (sp0 + -64) /\ getr R' 8 = wa 4096 /\ getr R' 9 = wa (a + 4096) /\ getr R' 10 = wa (a + 4096) /\
    getr R' 11 = wa 4096 /\ getr R' 12 = wa 3 /\ getr R' 18 = wa 621568 /\ getr R' 19 = wa 621712 /\ getr R' 20 = wa 18446744073709551615 /\
    getr R' 21 = wa v21 /\
    (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 a sh v21 Rg2 Rg10 Rg16 Rsp Asp Rv21 (S1 & S2 & S3 & S4 & S5 & S6 & S7) Ra Aa Rsh Msh W1 W2.
  assert (Rn : 2 <= Z.shiftl 2 sh <= 2^35).
  { rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_le_mono_r 2 (sh) 34 ltac:(lia) ltac:(lia)).
    pose proof (Z.pow_pos_nonneg 2 sh ltac:(lia) ltac:(lia)). lia. }
  assert (P1 : mmrr_pre R m (sp0 + -64) a 0 4096 (Z.shiftl 2 sh) 621568 621712 18446744073709551615 v21).
  { constructor; try assumption; try lia. }
  destruct (mmrr_pmmrr R m rom (sp0 + -64) a 0 4096 (Z.shiftl 2 sh) 621568 621712 18446744073709551615 v21 P1 ltac:(constructor))
    as (R1 & Hms1 & A1 & A2 & A8 & A9 & A10 & A11 & A16 & A18 & A19 & A20 & A21 & Ak1).
  change (mmrr_mem_pmmrr m R (sp0 + -64) a 0 4096 (Z.shiftl 2 sh) 621568 621712 18446744073709551615 v21) with m in Hms1.
  assert (P2 : mt8x_pre R1 m a sh (Z.shiftl 2 sh)) by (constructor; first [assumption | lia]).
  destruct (mt8x_pmt8x R1 m rom a sh (Z.shiftl 2 sh) P2 ltac:(constructor)) as (R2 & Hms2 & B1 & B8 & B9 & B10 & B11 & B12 & B19 & B20 & Bk2).
  replace (mt8x_mem_pmt8x m R1 a sh (Z.shiftl 2 sh)) with (rvx_mem m a sh) in Hms2 by reflexivity.
  exists R2. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
  split; [exact B1|]. split; [regk Bk2 2%nat; exact A2|]. split; [exact B8|]. split; [exact B9|]. split; [exact B10|].
  split; [exact B11|]. split; [exact B12|]. split; [regk Bk2 18%nat; exact A18|]. split; [exact B19|]. split; [exact B20|].
  split; [regk Bk2 21%nat; exact A21|].
  intros k Hk'. rewrite (Bk2 k ltac:(clear - Hk'; klist Hk')), (Ak1 k ltac:(clear - Hk'; klist Hk')). reflexivity.
Qed.
End AM6b.

Section AM6c.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_mpx : forall R m rom sp0 p,
  getr R 2 = wa (sp0 + -64) -> getr R 1 = wa 343320 -> getr R 10 = wa p -> getr R 11 = wa 4096 -> getr R 12 = wa 3 ->
  stk_ok SEGS m (wa (sp0 + -64)) 1024 -> 2^20 + 1024 <= sp0 <= 2^47 -> sp0 mod 16 = 0 ->
  4096 <= p <= 2^47 -> p mod 4096 = 0 -> rdn SEGS m (wa (0 + 621648)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  exists R', msteps SEGS (mkst R (wa 0x551cc) m rom) (mkst R' (wa 0x551fc) (mpw_store m sp0) rom) /\
    getr R' 17 = wa 226 /\ getr R' 10 = wa p /\ getr R' 11 = wa 4096 /\ getr R' 12 = wa 3 /\ getr R' 2 = wa (sp0 + -64 + -16) /\
    (forall k, In k [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 p Rg2 Rg1 Rg10 Rg11 Rg12 STK Rsp Asp Rp Ap Mpg.
  assert (P3 : mpw_pre R m (sp0 + -64) p) by (constructor; first [assumption | lia]).
  destruct (mpw_pmpw R m rom (sp0 + -64) p P3 ltac:(constructor)) as (R3 & Hms3 & C2 & C10 & C11 & C12 & C13 & C14 & C17 & Ck3).
  change (mpw_mem_pmpw m R (sp0 + -64) p) with (wbytes m (wa (sp0 + -64 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 1))))))) in Hms3.
  replace (wbytes m (wa (sp0 + -64 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 1)))))))
    with (mpw_store m sp0) in Hms3.
  2: { unfold mpw_store. replace (getr R (Z_to_bv 5 (Z.of_nat 1))) with (wa 343320) by (symmetry; litr2 Rg1; reflexivity).
       rewrite u_wa_small by lia. reflexivity. }
  exists R3. split; [exact Hms3|]. split; [exact C17|]. split; [exact C10|]. split; [exact C11|]. split; [exact C12|]. split; [exact C2|].
  intros k Hk'. apply Ck3. clear - Hk'. klist Hk'.
Qed.
End AM6c.

Section AM6d.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_mmw : forall R m rom sp0 sh,
  getr R 1 = wa 343108 -> getr R 2 = wa (sp0 + -64) -> getr R 8 = wa 4096 -> getr R 9 = wa (Z.shiftl 2 sh) ->
  getr R 10 = wa 0 -> getr R 11 = wa (4096 * Z.shiftl 2 sh) -> getr R 12 = wa 0 -> getr R 13 = wa 34 ->
  getr R 14 = wa 18446744073709551615 -> getr R 15 = wa 0 ->
  getr R 18 = wa 621568 -> getr R 19 = wa 621712 -> getr R 20 = wa 18446744073709551615 ->
  0 <= sh <= 34 -> stk_ok SEGS m (wa (sp0 + -64)) 1024 -> 2^20 + 1024 <= sp0 <= 2^47 -> sp0 mod 16 = 0 ->
  exists R' m', msteps SEGS (mkst R (wa 0x550e0) m rom) (mkst R' (wa 0x551a4) m' rom) /\
    getr R' 17 = wa 222 /\ getr R' 10 = wa 0 /\ getr R' 11 = wa (4096 * Z.shiftl 2 sh) /\ getr R' 12 = wa 0 /\ getr R' 13 = wa 34 /\
    getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\ getr R' 16 = wa 0 /\ getr R' 2 = wa (sp0 + -64 + -64) /\
    (forall k, In k [1; 3; 4; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    mmap_saves m' (sp0 + -64) 343108 4096 (Z.shiftl 2 sh) 621568 621712 18446744073709551615 (bv_unsigned (getr R 21)) /\
    (forall x, 0 <= x < 2^64 -> ~ (sp0 - 128 <= x < sp0 - 64) -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 sh A1 A2 A8 A9 A10 A11 A12 A13 A14 A15 A18 A19 A20 Rsh STK Rsp Asp.
  assert (P2 : mmwr_pre R m (sp0 + -64) 0 (4096 * Z.shiftl 2 sh) 0 34).
  { constructor; [exact A2 | exact A10 | exact A11 | exact A12 | exact A13 | exact A14 | exact A15 | exact STK | lia | lia | | lia | lia | lia].
    rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_le_mono_r 2 (sh) 34 ltac:(lia) ltac:(lia)). lia. }
  destruct (mmwr_pnfr R m rom (sp0 + -64) 0 (4096 * Z.shiftl 2 sh) 0 34 P2) as (R2 & Hms2 & B2 & B5 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & Bk2).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mmwr.RES_pnfr fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    apply sc_br_z. rewrite br_ne_z. cbn [zeval edenot]. rewrite (zatom R (VALS_mmwr (sp0 + -64) 0 (4096 * Z.shiftl 2 sh) 0 34) 36 34 eq_refl eq_refl) by lia.
    reflexivity. }
  set (m2 := mmwr_mem_pnfr m R (sp0 + -64) 0 (4096 * Z.shiftl 2 sh) 0 34) in *.
  exists R2, m2. split; [exact Hms2|].
  split; [exact B17|]. split; [exact B10|]. split; [exact B11|]. split; [exact B12|]. split; [exact B13|]. split; [exact B14|].
  split; [exact B15|]. split; [exact B16|]. split; [exact B2|].
  split; [intros k Hk'; apply Bk2; clear - Hk'; klist Hk'|].
  assert (W : forall k v, getr R (Z_to_bv 5 (Z.of_nat k)) = wa v -> 0 <= v < 2^64 -> bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat k))) = v).
  { intros k v E Hv. rewrite E. apply u_wa_small. exact Hv. }
  split.
  - unfold mmap_saves, m2, mmwr_mem_pnfr.
    assert (E1 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 1))) = 343108) by (apply W; [litr2 A1; reflexivity | lia]).
    assert (E8 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 8))) = 4096) by (apply W; [litr2 A8; reflexivity | lia]).
    assert (E9 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) = Z.shiftl 2 sh).
    { apply W; [litr2 A9; reflexivity|]. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_le_mono_r 2 (sh) 34 ltac:(lia) ltac:(lia)). lia. }
    assert (E18 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) = 621568) by (apply W; [litr2 A18; reflexivity | lia]).
    assert (E19 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19))) = 621712) by (apply W; [litr2 A19; reflexivity | lia]).
    assert (E20 : bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) = 18446744073709551615) by (apply W; [litr2 A20; reflexivity | lia]).
    rewrite E1, E8, E9, E18, E19, E20.
    repeat split; repeat (rewrite rdn_wbytes_disjoint; [| side | side]); first [ (apply rdn_wbytes_hit8; side) | (rewrite wa_u; apply rdn_wbytes_hit8; side) ].
  - split.
    + intros x Hx Hn. unfold m2, mmwr_mem_pnfr. do 7 (rewrite MngWb.wbytes_out by side). reflexivity.
    + unfold m2, mmwr_mem_pnfr. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bdx : forall R m rom sp0 can ra s0 s1 s2 s3 s4 ar sh,
  am_frame R m sp0 can ra s0 s1 s2 s3 s4 -> getr R 8 = wa 4096 ->
  rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa 18446744073709551615)) ->
  0 <= ar <= 2^64-1 -> rdn SEGS m (wa (0 + 621792)) 8 = Some (word_to_le_bytes 8 (wa ar)) ->
  0 <= sh <= 34 -> rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ->
  exists R', msteps SEGS (mkst R (wa 0x53b68) m rom) (mkst R' (wa 0x550e0) m rom) /\
    getr R' 1 = wa 343108 /\ getr R' 2 = wa (sp0 + -64) /\ getr R' 8 = wa 4096 /\ getr R' 9 = wa (Z.shiftl 2 sh) /\
    getr R' 10 = wa 0 /\ getr R' 11 = wa (4096 * Z.shiftl 2 sh) /\ getr R' 12 = wa 0 /\ getr R' 13 = wa 34 /\
    getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\
    getr R' 18 = wa 621568 /\ getr R' 19 = wa 621712 /\ getr R' 20 = wa 18446744073709551615 /\
    (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 can ra s0 s1 s2 s3 s4 ar sh F R8 Mac Mbk Rar Mar Rsh Msh.
  assert (P1 : mt3w_pre R m 0 18446744073709551615 ar sh)
    by (constructor; [exact R8 | exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | lia | lia | exact Rar | lia | exact Mac | exact Mbk | exact Mar | exact Msh]).
  destruct (mt3w_pmt3dw R m rom 0 18446744073709551615 ar sh P1) as (R1 & Hms1 & A1 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A19 & A20 & Ak1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt3w.RES_pmt3dw fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; first [rewrite br_eq_z | rewrite br_ne_z]; cbn [zeval edenot].
    all: rewrite ?(zatom R (VALS_mt3w 0 18446744073709551615 ar sh) 32 0 eq_refl eq_refl) by lia.
    all: rewrite ?(zatom R (VALS_mt3w 0 18446744073709551615 ar sh) 33 18446744073709551615 eq_refl eq_refl) by lia.
    all: reflexivity. }
  change (mt3w_mem_pmt3dw m R 0 18446744073709551615 ar sh) with m in Hms1.
  exists R1. split; [exact Hms1|].
  split; [exact A1|]. split; [regk Ak1 2%nat; exact (mf_R2 _ _ _ _ _ _ _ _ _ _ F)|]. split; [exact A8|]. split; [exact A9|].
  split; [exact A10|]. split; [exact A11|]. split; [exact A12|]. split; [exact A13|]. split; [exact A14|]. split; [exact A15|].
  split; [regk Ak1 18%nat; exact (mf_R18 _ _ _ _ _ _ _ _ _ _ F)|]. split; [exact A19|]. split; [exact A20|].
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.
End AM6d.

Section AM6e.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bcx : forall R m rom sp0 can ra s0 s1 s2 s3 s4 ar sh bk,
  am_frame R m sp0 can ra s0 s1 s2 s3 s4 -> getr R 8 = wa 4096 ->
  rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  4096 <= bk <= 2^47 -> rdn SEGS m (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa bk)) ->
  0 <= ar <= 2^64-1 -> rdn SEGS m (wa (0 + 621792)) 8 = Some (word_to_le_bytes 8 (wa ar)) ->
  0 <= sh <= 34 -> rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ->
  exists R', msteps SEGS (mkst R (wa 0x53b68) m rom) (mkst R' (wa 0x53b8c) m rom) /\
    getr R' 17 = wa 214 /\ getr R' 10 = wa (bk + 4096) /\ getr R' 9 = wa (bk + 4096) /\ getr R' 8 = wa 4096 /\ getr R' 19 = wa 621712 /\
    (forall k, In k [1; 2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 can ra s0 s1 s2 s3 s4 ar sh bk F R8 Mac Rbk Mbk Rar Mar Rsh Msh.
  assert (P1 : mt3w_pre R m 0 bk ar sh)
    by (constructor; [exact R8 | exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | lia | lia | exact Rar | lia | exact Mac | exact Mbk | exact Mar | exact Msh]).
  destruct (mt3w_pmt3cw R m rom 0 bk ar sh P1) as (R1 & Hms1 & A8 & A9 & A10 & A11 & A17 & A19 & Ak1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt3w.RES_pmt3cw fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; first [rewrite br_eq_z | rewrite br_ne_z]; cbn [zeval edenot].
    all: rewrite ?(zatom R (VALS_mt3w 0 bk ar sh) 32 0 eq_refl eq_refl) by lia.
    all: rewrite ?(zatom R (VALS_mt3w 0 bk ar sh) 33 bk eq_refl eq_refl) by lia.
    all: first [ reflexivity | (apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia) ]. }
  change (mt3w_mem_pmt3cw m R 0 bk ar sh) with m in Hms1.
  exists R1. split; [exact Hms1|]. split; [exact A17|]. split; [exact A10|]. split; [exact A9|]. split; [exact A8|]. split; [exact A19|].
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bcr : forall R m rom res nb sh,
  getr R 8 = wa 4096 -> getr R 9 = wa nb -> getr R 10 = wa res -> getr R 19 = wa 621712 ->
  0 <= res <= 2^64-1 -> 8192 <= nb <= 2^47 -> res <> nb -> 0 <= sh <= 34 ->
  rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) -> rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621760 + d)) k = true) ->
  exists R', msteps SEGS (mkst R (wa 0x53b90) m rom) (mkst R' (wa 0x550e0) (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa 18446744073709551615))) rom) /\
    getr R' 1 = wa 343108 /\ getr R' 8 = wa 4096 /\ getr R' 9 = wa (Z.shiftl 2 sh) /\ getr R' 10 = wa 0 /\ getr R' 11 = wa (4096 * Z.shiftl 2 sh) /\
    getr R' 12 = wa 0 /\ getr R' 13 = wa 34 /\ getr R' 14 = wa 18446744073709551615 /\ getr R' 15 = wa 0 /\ getr R' 19 = wa 621712 /\
    getr R' 20 = wa 18446744073709551615 /\
    (forall k, In k [2; 3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom res nb sh R8 R9 R10 R19 Rres Rnb Hne Rsh M3 M4 W5 W6.
  assert (P1 : mt6_pre R m res nb sh) by (constructor; first [assumption | lia]).
  destruct (mt6_pmt6r R m rom res nb sh P1) as (R1 & Hms1 & A1 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A19 & A20 & Ak1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt6.RES_pmt6r fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot].
    rewrite (zatom R (VALS_mt6 res nb sh) 32 res eq_refl eq_refl) by lia. rewrite (zatom R (VALS_mt6 res nb sh) 33 nb eq_refl eq_refl) by lia.
    apply Z.eqb_neq. rewrite !Z.mod_small by lia. exact Hne. }
  replace (mt6_mem_pmt6r m R res nb sh) with (wbytes m (wa (0 + 622640)) (word_to_le_bytes 8 (wa 18446744073709551615))) in Hms1 by reflexivity.
  exists R1. split; [exact Hms1|].
  do 11 (split; [assumption|]).
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_bcg : forall R m rom nb sh,
  getr R 8 = wa 4096 -> getr R 9 = wa nb -> getr R 10 = wa nb -> getr R 19 = wa 621712 ->
  8192 <= nb <= 2^47 -> 0 <= sh <= 34 ->
  rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) -> rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621760 + d)) k = true) ->
  exists R', msteps SEGS (mkst R (wa 0x53b90) m rom) (mkst R' (wa 0x53c78) (mt6_mem_pmt6g m R nb nb sh) rom) /\
    getr R' 8 = wa 1 /\ getr R' 9 = wa (nb + -4096) /\ getr R' 19 = wa 621712 /\
    (forall k, In k [1; 2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom nb sh R8 R9 R10 R19 Rnb Rsh M3 M4 W5 W6.
  assert (P1 : mt6_pre R m nb nb sh) by (constructor; first [assumption | lia]).
  destruct (mt6_pmt6g R m rom nb nb sh P1) as (R1 & Hms1 & A8 & A9 & A10 & A19 & Ak1).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt6.RES_pmt6g fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
    apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot].
    rewrite (zatom R (VALS_mt6 nb nb sh) 32 nb eq_refl eq_refl) by lia. rewrite (zatom R (VALS_mt6 nb nb sh) 33 nb eq_refl eq_refl) by lia.
    apply Z.eqb_refl. }
  exists R1. split; [exact Hms1|]. split; [exact A8|]. split; [exact A9|]. split; [exact A19|].
  intros k Hk'. apply Ak1. clear - Hk'. klist Hk'.
Qed.
End AM6e.
