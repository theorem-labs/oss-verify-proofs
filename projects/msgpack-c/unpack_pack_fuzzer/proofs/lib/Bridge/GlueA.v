(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.PropExec ALib.MState ALib.Frame ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Mem State Step Plan ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require RegsEqv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP CtrLib CtrA CtrFX.
Open Scope Z_scope.
Unset Lia Cache.

Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module AMem := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section GlueA.
Variable segs : list Segment.
Variable OPS : optable.

Lemma ms_formA : forall E st ms mo, st_ok segs OPS E st ms mo -> s_resv st = RNone ->
  ms = AM.MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (AP.seg_rom segs).
Proof.
  intros E st ms mo HS HR.
  pose proof (so_svc _ _ _ _ _ _ HS) as SV. pose proof (so_resv _ _ _ _ _ _ HS) as RV. rewrite HR in RV. cbn in RV.
  pose proof (so_rom _ _ _ _ _ _ HS) as RO. pose proof (so_pc _ _ _ _ _ _ HS) as PC.
  rewrite (AM.MS_eta ms SV). cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom AM.MS].
  rewrite RV, PC, RO. reflexivity.
Qed.

Lemma getr_RA : forall E st ms mo, st_ok segs OPS E st ms mo ->
  forall x, AP.getr (ms_regs ms) (reg_of_r5 x) = den E (getr st x).
Proof.
  intros E st ms mo HS x. pose proof (so_regs _ _ _ _ _ _ HS x) as R. unfold rget in R. cbn [c_regs] in R.
  unfold AP.getr, getr. unfold is_x0 in R.
  destruct x; cbn [reg_of_r5 r5_to_Z] in R |- *; first [exact R | rewrite <- R; reflexivity].
Qed.

Definition mkR_ofA (R : bvmap 5 word) : bvmap 5 word :=
  AF.mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
      (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
      (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
      (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31).

Lemma realizes_to_mkRA : forall R F pc fc m ro mo (T : ShapeAlg.TSet),
  ShapeAlg.realizes segs (mkCfg (AM.MS (mkR_ofA R) F pc fc None m ro) mo) T ->
  ShapeAlg.realizes segs (mkCfg (AM.MS R F pc fc None m ro) mo) T.
Proof. intros R F pc fc m ro mo T H. exact (RegsEqv.realizes_to_mkR segs R F pc fc m ro mo T H). Qed.

Lemma rb_mrdA : forall m a, rb segs m a = AMem.mrd segs m (AMem.wa a).
Proof. reflexivity. Qed.
Lemma wb_wviewA : forall m a, wb segs m a = true <-> wview segs m (AMem.wa a) <> None.
Proof. intros m a. unfold wb, AMem.wa. destruct (wview segs m (Z_to_bv 64 a)); split; congruence. Qed.

Lemma w2Zs_wsub_small : forall a b, - two63 <= w2Zs a - w2Zs b < two63 -> w2Zs (wsub a b) = w2Zs a - w2Zs b.
Proof.
  intros a b H. rewrite (w2Zs_eq (wsub a b)), w2Z_wt, wsub_ok.
  rewrite (w2Zs_eq a), (w2Zs_eq b), (w2Z_wt a), (w2Z_wt b) in H |- *.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb. unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z a)), (Z.leb_spec 9223372036854775808 (w2Z b));
  destruct (Z_lt_le_dec (w2Z a - w2Z b) 0);
  try (replace (w2Z a - w2Z b) with ((w2Z a - w2Z b + 18446744073709551616) + (-1) * 18446744073709551616) by lia;
       rewrite Z.mod_add, Z.mod_small by lia;
       destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b + 18446744073709551616)); lia);
  try (rewrite (Z.mod_small (w2Z a - w2Z b)) by lia; destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b)); lia).
Qed.

Lemma stack_sound : forall E st ms mo need ksp klo1,
  st_ok segs OPS E st ms mo -> to_Z need < 2 ^ 32 -> CtrA.stack_ok st need = Some (ksp, klo1) ->
  exists off r1, getr st X2 = VP STACK_ID off /\ IMap.find STACK_ID (s_regs st) = Some r1
    /\ rg_w r1 = true /\ rg_bg r1 = BGNone /\ okey off = Some ksp /\ klo1 = rg_lo r1 /\ keyZ ksp mod 16 = 0
    /\ keyZ ksp < 0
    /\ bv_unsigned (den E (getr st X2)) = bv_unsigned (ev E STACK_ID) + keyZ ksp
    /\ 0 <= bv_unsigned (ev E STACK_ID) + loZ r1
    /\ bv_unsigned (ev E STACK_ID) + loZ r1 <= bv_unsigned (ev E STACK_ID) + keyZ ksp - to_Z need
    /\ bv_unsigned (ev E STACK_ID) + keyZ ksp <= bv_unsigned (ev E STACK_ID) + hiZ E r1 < 2 ^ 64
    /\ AF.stk segs (ms_mem ms) (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + hiZ E r1).
Proof.
  intros E st ms mo need ksp klo1 HS Hneed H. unfold CtrA.stack_ok in H.
  destruct (getr st X2) as [|k off| | | | | | | | |] eqn:HX2; try discriminate.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
  destruct (PrimInt63.eqb k STACK_ID) eqn:HK; [|discriminate]. apply Uint63.eqb_correct in HK. subst k.
  destruct (rg_w r1) eqn:HW; [|discriminate]. destruct (rg_bg r1) eqn:HBG; try discriminate. cbn [negb orb] in H.
  destruct (okey off) as [ksp'|] eqn:Hksp; [|discriminate].
  destruct (okey (wsub off (wlit need))) as [klo|] eqn:Hklo; [|discriminate].
  destruct (rg_hi r1) as [h| | | | | | | | | |] eqn:Hhi; try discriminate.
  destruct (okey h) as [kh|] eqn:Hkh; [|discriminate].
  destruct (kleb (rg_lo r1) klo) eqn:L1; [|discriminate]. destruct (kleb ksp' kh) eqn:L2; [|discriminate].
  destruct (PrimInt63.eqb (PrimInt63.land ksp' 15) 0) eqn:AL; [|discriminate].
  destruct (PrimInt63.leb bit62i ksp') eqn:NEG; [|discriminate]. cbn [andb] in H. injection H as -> <-.
  rewrite kleb_keyZ in L1, L2. apply Z.leb_le in L1. apply Z.leb_le in L2.
  destruct (okey_sound _ _ Hksp) as [Eksp Rksp]. destruct (okey_sound _ _ Hklo) as [Eklo Rklo]. destruct (okey_sound _ _ Hkh) as [Ekh Rkh].
  rewrite !half63 in Rksp, Rklo, Rkh.
  assert (Eneed : w2Zs (wlit need) = to_Z need) by (rewrite w2Zs_eq, wlit_ok; cbn [wt wlit]; lia).
  pose proof (int_range need) as Rn. rewrite two63_eq in Rn.
  assert (Eklo' : keyZ klo = keyZ ksp - to_Z need).
  { rewrite Eklo, w2Zs_wsub_small; [rewrite Eneed, Eksp; reflexivity|].
    rewrite Eneed, <- Eksp. unfold two63 in *. lia. }
  pose proof (so_reg _ _ _ _ _ _ HS _ _ Hr1) as RO.
  pose proof (ro_range _ _ _ _ _ _ RO eq_refl) as [RLO RHI]. unfold two64 in RHI.
  assert (Ehi : keyZ kh <= hiZ E r1).
  { unfold hiZ. rewrite Hhi, unsigned_VL, Ekh, w2Zs_eq. unfold two64. destruct (wt h); lia. }
  exists off, r1. split; [reflexivity|]. split; [reflexivity|]. split; [exact HW|]. split; [exact HBG|]. split; [exact Hksp|]. split; [reflexivity|]. split.
  { apply Uint63.eqb_correct in AL. pose proof (land_mk ksp 4%uint63 ltac:(change (to_Z 4%uint63) with 4; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 4) 1)%uint63 with 15%uint63 in LM. rewrite AL in LM.
    change (to_Z 0%uint63) with 0 in LM. change (2 ^ to_Z 4%uint63) with 16 in LM.
    destruct (keyZ_cases ksp) as [[_ ->]|[_ ->]]; [lia|].
    replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) by lia. rewrite Z.mod_add by lia. lia. }
  split. { apply Uint63.leb_spec in NEG. rewrite to_Z_bit62i in NEG. destruct (keyZ_cases ksp) as [[R EK]|[R EK]]; [lia| rewrite EK; lia]. }
  assert (Esp : bv_unsigned (den E (VP STACK_ID off)) = bv_unsigned (ev E STACK_ID) + keyZ ksp).
  { rewrite den_VP, <- Eksp. unfold loZ in *. apply Z.mod_small. unfold two64. lia. }
  split; [exact Esp|]. unfold loZ in *. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (ro_valid _ _ _ _ _ _ RO eq_refl a Ha) as (V1 & V2 & _).
  split; [apply wb_wviewA; apply V2; exact HW|]. rewrite rb_mrdA in V1. destruct (AMem.mrd segs (ms_mem ms) (AMem.wa a)); [eexists; reflexivity| congruence].
Qed.

Lemma wmono_ofA : forall m m' : word -> option byte,
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) -> AF.wmono segs m m'.
Proof.
  intros m m' H x Hx. unfold wview in *.
  pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with two64 in R.
  pose proof (H (bv_unsigned x) R) as Hm. rewrite Z_to_bv_bv_unsigned in Hm.
  destruct (m x) as [b|] eqn:E.
  - destruct (m' x); [congruence| exfalso; apply Hm; congruence].
  - destruct (m' x); [congruence| exact Hx].
Qed.

End GlueA.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP CtrLib CtrA CtrFX.
Open Scope Z_scope.
Unset Lia Cache.

Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module AMem := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section GlueA.
Variable segs : list Segment.
Variable OPS : optable.

Lemma ms_formA : forall E st ms mo, st_ok segs OPS E st ms mo -> s_resv st = RNone ->
  ms = AM.MS (ms_regs ms) (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (AP.seg_rom segs).
Proof.
  intros E st ms mo HS HR.
  pose proof (so_svc _ _ _ _ _ _ HS) as SV. pose proof (so_resv _ _ _ _ _ _ HS) as RV. rewrite HR in RV. cbn in RV.
  pose proof (so_rom _ _ _ _ _ _ HS) as RO. pose proof (so_pc _ _ _ _ _ _ HS) as PC.
  rewrite (AM.MS_eta ms SV). cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom AM.MS].
  rewrite RV, PC, RO. reflexivity.
Qed.

Lemma getr_RA : forall E st ms mo, st_ok segs OPS E st ms mo ->
  forall x, AP.getr (ms_regs ms) (reg_of_r5 x) = den E (getr st x).
Proof.
  intros E st ms mo HS x. pose proof (so_regs _ _ _ _ _ _ HS x) as R. unfold rget in R. cbn [c_regs] in R.
  unfold AP.getr, getr. unfold is_x0 in R.
  destruct x; cbn [reg_of_r5 r5_to_Z] in R |- *; first [exact R | rewrite <- R; reflexivity].
Qed.

Definition mkR_ofA (R : bvmap 5 word) : bvmap 5 word :=
  AF.mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
      (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
      (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
      (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31).

Lemma realizes_to_mkRA : forall R F pc fc m ro mo (T : ShapeAlg.TSet),
  ShapeAlg.realizes segs (mkCfg (AM.MS (mkR_ofA R) F pc fc None m ro) mo) T ->
  ShapeAlg.realizes segs (mkCfg (AM.MS R F pc fc None m ro) mo) T.
Proof. intros R F pc fc m ro mo T H. exact (RegsEqv.realizes_to_mkR segs R F pc fc m ro mo T H). Qed.

Lemma rb_mrdA : forall m a, rb segs m a = AMem.mrd segs m (AMem.wa a).
Proof. reflexivity. Qed.
Lemma wb_wviewA : forall m a, wb segs m a = true <-> wview segs m (AMem.wa a) <> None.
Proof. intros m a. unfold wb, AMem.wa. destruct (wview segs m (Z_to_bv 64 a)); split; congruence. Qed.

Lemma w2Zs_wsub_small : forall a b, - two63 <= w2Zs a - w2Zs b < two63 -> w2Zs (wsub a b) = w2Zs a - w2Zs b.
Proof.
  intros a b H. rewrite (w2Zs_eq (wsub a b)), w2Z_wt, wsub_ok.
  rewrite (w2Zs_eq a), (w2Zs_eq b), (w2Z_wt a), (w2Z_wt b) in H |- *.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb. unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z a)), (Z.leb_spec 9223372036854775808 (w2Z b));
  destruct (Z_lt_le_dec (w2Z a - w2Z b) 0);
  try (replace (w2Z a - w2Z b) with ((w2Z a - w2Z b + 18446744073709551616) + (-1) * 18446744073709551616) by lia;
       rewrite Z.mod_add, Z.mod_small by lia;
       destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b + 18446744073709551616)); lia);
  try (rewrite (Z.mod_small (w2Z a - w2Z b)) by lia; destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b)); lia).
Qed.

Lemma stack_sound : forall E st ms mo need ksp klo1,
  st_ok segs OPS E st ms mo -> to_Z need < 2 ^ 32 -> CtrA.stack_ok st need = Some (ksp, klo1) ->
  exists off r1, getr st X2 = VP STACK_ID off /\ IMap.find STACK_ID (s_regs st) = Some r1
    /\ rg_w r1 = true /\ rg_bg r1 = BGNone /\ okey off = Some ksp /\ klo1 = rg_lo r1 /\ keyZ ksp mod 16 = 0
    /\ keyZ ksp < 0
    /\ bv_unsigned (den E (getr st X2)) = bv_unsigned (ev E STACK_ID) + keyZ ksp
    /\ 0 <= bv_unsigned (ev E STACK_ID) + loZ r1
    /\ bv_unsigned (ev E STACK_ID) + loZ r1 <= bv_unsigned (ev E STACK_ID) + keyZ ksp - to_Z need
    /\ bv_unsigned (ev E STACK_ID) + keyZ ksp <= bv_unsigned (ev E STACK_ID) + hiZ E r1 < 2 ^ 64
    /\ AF.stk segs (ms_mem ms) (bv_unsigned (ev E STACK_ID) + loZ r1) (bv_unsigned (ev E STACK_ID) + hiZ E r1).
Proof.
  intros E st ms mo need ksp klo1 HS Hneed H. unfold CtrA.stack_ok in H.
  destruct (getr st X2) as [|k off| | | | | | | | |] eqn:HX2; try discriminate.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|] eqn:Hr1; [|discriminate].
  destruct (PrimInt63.eqb k STACK_ID) eqn:HK; [|discriminate]. apply Uint63.eqb_correct in HK. subst k.
  destruct (rg_w r1) eqn:HW; [|discriminate]. destruct (rg_bg r1) eqn:HBG; try discriminate. cbn [negb orb] in H.
  destruct (okey off) as [ksp'|] eqn:Hksp; [|discriminate].
  destruct (okey (wsub off (wlit need))) as [klo|] eqn:Hklo; [|discriminate].
  destruct (rg_hi r1) as [h| | | | | | | | | |] eqn:Hhi; try discriminate.
  destruct (okey h) as [kh|] eqn:Hkh; [|discriminate].
  destruct (kleb (rg_lo r1) klo) eqn:L1; [|discriminate]. destruct (kleb ksp' kh) eqn:L2; [|discriminate].
  destruct (PrimInt63.eqb (PrimInt63.land ksp' 15) 0) eqn:AL; [|discriminate].
  destruct (PrimInt63.leb bit62i ksp') eqn:NEG; [|discriminate]. cbn [andb] in H. injection H as -> <-.
  rewrite kleb_keyZ in L1, L2. apply Z.leb_le in L1. apply Z.leb_le in L2.
  destruct (okey_sound _ _ Hksp) as [Eksp Rksp]. destruct (okey_sound _ _ Hklo) as [Eklo Rklo]. destruct (okey_sound _ _ Hkh) as [Ekh Rkh].
  rewrite !half63 in Rksp, Rklo, Rkh.
  assert (Eneed : w2Zs (wlit need) = to_Z need) by (rewrite w2Zs_eq, wlit_ok; cbn [wt wlit]; lia).
  pose proof (int_range need) as Rn. rewrite two63_eq in Rn.
  assert (Eklo' : keyZ klo = keyZ ksp - to_Z need).
  { rewrite Eklo, w2Zs_wsub_small; [rewrite Eneed, Eksp; reflexivity|].
    rewrite Eneed, <- Eksp. unfold two63 in *. lia. }
  pose proof (so_reg _ _ _ _ _ _ HS _ _ Hr1) as RO.
  pose proof (ro_range _ _ _ _ _ _ RO eq_refl) as [RLO RHI]. unfold two64 in RHI.
  assert (Ehi : keyZ kh <= hiZ E r1).
  { unfold hiZ. rewrite Hhi, unsigned_VL, Ekh, w2Zs_eq. unfold two64. destruct (wt h); lia. }
  exists off, r1. split; [reflexivity|]. split; [reflexivity|]. split; [exact HW|]. split; [exact HBG|]. split; [exact Hksp|]. split; [reflexivity|]. split.
  { apply Uint63.eqb_correct in AL. pose proof (land_mk ksp 4%uint63 ltac:(change (to_Z 4%uint63) with 4; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 4) 1)%uint63 with 15%uint63 in LM. rewrite AL in LM.
    change (to_Z 0%uint63) with 0 in LM. change (2 ^ to_Z 4%uint63) with 16 in LM.
    destruct (keyZ_cases ksp) as [[_ ->]|[_ ->]]; [lia|].
    replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) by lia. rewrite Z.mod_add by lia. lia. }
  split. { apply Uint63.leb_spec in NEG. rewrite to_Z_bit62i in NEG. destruct (keyZ_cases ksp) as [[R EK]|[R EK]]; [lia| rewrite EK; lia]. }
  assert (Esp : bv_unsigned (den E (VP STACK_ID off)) = bv_unsigned (ev E STACK_ID) + keyZ ksp).
  { rewrite den_VP, <- Eksp. unfold loZ in *. apply Z.mod_small. unfold two64. lia. }
  split; [exact Esp|]. unfold loZ in *. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (ro_valid _ _ _ _ _ _ RO eq_refl a Ha) as (V1 & V2 & _).
  split; [apply wb_wviewA; apply V2; exact HW|]. rewrite rb_mrdA in V1. destruct (AMem.mrd segs (ms_mem ms) (AMem.wa a)); [eexists; reflexivity| congruence].
Qed.

Lemma wmono_ofA : forall m m' : word -> option byte,
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) -> AF.wmono segs m m'.
Proof.
  intros m m' H x Hx. unfold wview in *.
  pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with two64 in R.
  pose proof (H (bv_unsigned x) R) as Hm. rewrite Z_to_bv_bv_unsigned in Hm.
  destruct (m x) as [b|] eqn:E.
  - destruct (m' x); [congruence| exfalso; apply Hm; congruence].
  - destruct (m' x); [congruence| exact Hx].
Qed.

End GlueA.
End TwinB.
