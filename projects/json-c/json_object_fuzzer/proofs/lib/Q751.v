(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq3.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section LoopKit.
Variable L : heap_layout_A.
Notation segs := (hl_segs L).
Notation shad := (QZsi.shad L).
Notation fr_ivs := (QZsi.fr_ivs L).
Variable HIx : heap_iface_A L.

Definition stack_malloc_text5 (J : aj_base segs) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (k bytes lo : Z),
HEAPA L HIx A LB LM FR B m c ->
(0 <= k <= 2 \/ (k = 3 /\ hl_stack_malloc L 3 <> 0 /\ Z.of_nat (length FR) < 2048)) -> 1 <= bytes <= fr_size k -> bytes mod 8 = 0 ->
(Z.of_nat (length FR) < 4096) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top L HIx + 64 ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 bytes ->
(forall ms' m' c' A' (Fr : Z),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 Fr) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
Fr <> 0 ->
(exists junk, rw_cells segs m' Fr [CB (Z.to_nat (fr_size k - 8)) junk]) ->
bytes_at segs m' (shad Fr) (repeat (Z_to_bv 8 0) (Z.to_nat (fr_shadow_len k))) ->
HEAPA L HIx A' LB LM ((Fr, k) :: FR) B m' c' ->
AJ5of L J A' T c' ms') ->
AJ5of L J A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_stack_malloc L k)) fc None m (seg_rom segs)).
Definition frame_release_text5 (J : aj_base segs) : Prop :=
forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config)
(T : TSet) (A : ASA L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (Fr k fp pc : Z) (rX : bv 5),
HEAPA L HIx A LB LM FR B m c -> In (Fr, k) FR ->
bytes_at segs m (Fr + fr_size k - 8) (le8 (Z_to_bv 64 fp)) ->
0 <= fp < 2^64 ->
Sem.reg_get R rX = Z_to_bv 64 fp ->
bv_unsigned rX <> 0 ->
code_at segs pc [0x23 + Z.shiftl (bv_unsigned rX) 15] ->
(forall m' c' A',
model_vm_only (cfg_model c) (cfg_model c') ->
HEAPA L HIx A' LB LM (fr_remove Fr FR) B m' c' ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
AJ5of L J A' T c' (MS R F (Z_to_bv 64 (pc + 4)) fc None m' (seg_rom segs))) ->
AJ5of L J A T c (MS R F (Z_to_bv 64 pc) fc None m (seg_rom segs)).

Record loop_kit5 (VV : config -> machine_state -> Prop) (T : TSet) : Type := LK5 {
lk_J : aj_base segs;
lk_wit : TSet -> Prop;
lk_Tw : TSet;
lk_Tn : TSet;
lk_w : lk_wit lk_Tw;
lk_n : ~ lk_wit lk_Tn;
lk_ck : forall c, CK (hiA_J L HIx) c -> CK lk_J c;
lk_cnext : forall c c', CNEXT lk_J c c' -> CNEXT (hiA_J L HIx) c c';
lk_exit : forall X c ms, AJ (hiA_J L HIx) T c ms -> AJ lk_J X c ms;
lk_back : forall c ms, ~ VV c ms -> evt segs (VV c) ms -> AJ lk_J lk_Tn c ms;
lk_stack_malloc : stack_malloc_text5 lk_J;
lk_frame_release : frame_release_text5 lk_J;
lk_getrandom : forall (F : FPF) (fc : FPC), @aj_getrandom_tagged_stmt F fc segs lk_J lk_wit
}.

Definition heap_loop_rule5 : Prop :=
forall (VV : config -> machine_state -> Prop) (T : TSet) c0 ms0,
VV c0 ms0 ->
(forall K : loop_kit5 VV T, forall c ms, VV c ms -> AJ (lk_J VV T K) (lk_Tw VV T K) c ms) ->
AJ (hiA_J L HIx) T c0 ms0.

End LoopKit.

Section LoopKit6.
Variable L : heap_layout_A.
Notation segs := (hl_segs L).
Variable H6 : QZsi.heap_iface_A L.
Notation J6 := (QZsi.hiA_J L H6).

Record loop_kit6 (VV : config -> machine_state -> Prop) (T : TSet) : Type := LK6 {
lk6_J : aj_base segs;
lk6_wit : TSet -> Prop;
lk6_Tw : TSet;
lk6_Tn : TSet;
lk6_w : lk6_wit lk6_Tw;
lk6_n : ~ lk6_wit lk6_Tn;
lk6_ck : forall c, CK J6 c -> CK lk6_J c;
lk6_cnext : forall c c', CNEXT lk6_J c c' -> CNEXT J6 c c';
lk6_exit : forall X c ms, AJ J6 T c ms -> AJ lk6_J X c ms;
lk6_back : forall c ms, ~ VV c ms -> evt segs (VV c) ms -> AJ lk6_J lk6_Tn c ms;
lk6_tier1 : QZsi.hia_tier1 L lk6_J (QZsi.ASA L H6) (QZsi.HEAPA L H6) (QZsi.hiA_top L H6);
lk6_getrandom : forall (F : FPF) (fc : FPC), @aj_getrandom_tagged_stmt F fc segs lk6_J lk6_wit
}.

Definition heap_loop_rule6 : Prop :=
forall (VV : config -> machine_state -> Prop) (T : TSet) c0 ms0,
VV c0 ms0 ->
(forall K : loop_kit6 VV T, forall c ms, VV c ms -> AJ (lk6_J VV T K) (lk6_Tw VV T K) c ms) ->
AJ J6 T c0 ms0.

Lemma kit5_stack_malloc : forall VV T (K : loop_kit6 VV T), stack_malloc_text5 L (hi5_of_v6 L H6) (lk6_J VV T K).
Proof.
intros VV T K. unfold stack_malloc_text5. cbn [HEAPA hi5_of_v6 hiA_top ASA].
intros until lo. intros HP K02 BYTES MOD8 FRL ST LO LOS SPA HT TP A0 KK HGP.
destruct HP as (B6 & HP6 & LK).
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
eapply (QZsi.t1_hiA_stack_malloc L _ _ _ _ (lk6_tier1 VV T K)) with (B := B6) (k := k) (bytes := bytes) (lo := lo);
[ exact HP6 | exact K02 | exact BYTES | exact MOD8 | exact FRL | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact TP | exact GP | exact A0 | ].
intros ms' m' A' Fr RS ST' HPR FRNZ BLK SHB HP'.
eapply (KK ms' m' c A' Fr RS (model_vm_only_refl _) ST' HPR FRNZ BLK SHB).
- eexists; split; [exact HP' | exact LK].
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.

Lemma kit5_frame_release : forall VV T (K : loop_kit6 VV T), frame_release_text5 L (hi5_of_v6 L H6) (lk6_J VV T K).
Proof.
intros VV T K. unfold frame_release_text5. cbn [HEAPA hi5_of_v6 hiA_top ASA].
intros until rX. intros HP HIN BYTES FPR REG RXNZ CODE KK HGP.
destruct HP as (B6 & HP6 & LK).
eapply (QZsi.t1_hiA_frame_release L _ _ _ _ (lk6_tier1 VV T K)) with (B := B6) (Fr := Fr) (k := k) (fp := fp) (rX := rX);
[ exact HP6 | exact HIN | exact BYTES | exact FPR | exact REG | exact RXNZ | exact CODE | ].
intros m' A' HP' AGR WV.
eapply (KK m' c A'); [ apply model_vm_only_refl | eexists; split; [exact HP' | exact LK] | exact AGR | exact WV | exact HGP ].
Qed.

Definition kit5_of_6 VV T (K : loop_kit6 VV T) : loop_kit5 L (hi5_of_v6 L H6) VV T :=
LK5 L (hi5_of_v6 L H6) VV T (lk6_J VV T K) (lk6_wit VV T K) (lk6_Tw VV T K) (lk6_Tn VV T K) (lk6_w VV T K) (lk6_n VV T K)
(lk6_ck VV T K) (lk6_cnext VV T K) (lk6_exit VV T K) (lk6_back VV T K)
(kit5_stack_malloc VV T K) (kit5_frame_release VV T K) (lk6_getrandom VV T K).

Theorem loop_rule5_of_6 : heap_loop_rule6 -> heap_loop_rule5 L (hi5_of_v6 L H6).
Proof.
intros R6 VV T c0 ms0 H0 Hbody. apply (R6 VV T c0 ms0 H0).
intros K c ms HV. exact (Hbody (kit5_of_6 VV T K) c ms HV).
Qed.

End LoopKit6.
End RC__1.
