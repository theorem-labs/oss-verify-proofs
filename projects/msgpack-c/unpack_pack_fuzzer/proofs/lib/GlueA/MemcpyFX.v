(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemcpyC MemOps MemsetFX TolC TolFX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib MemcpyC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module MemcpyFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Definition ov_read_bytes_inv := TolFX.ov_read_bytes_inv segs.
Definition stored_is_loaded := TolFX.stored_is_loaded.

Lemma copy_bytes_sound : forall fuel i src dst sofs dofs len st stn E ms mo,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  copy_bytes segs fuel i src dst sofs dofs len st = Some stn ->
  to_Z i <= to_Z len <= 4096 ->
  let S := bv_unsigned (den E src) in let D := bv_unsigned (den E dst) in
  D + to_Z len < two64 -> S + to_Z len < two64 -> (S + to_Z len <= D \/ D + to_Z len <= S) ->
  exists m', St.st_ok segs OPS E stn (ms_with_mem ms m') mo
    /\ (forall a, 0 <= a < two64 -> ~ (D + to_Z i <= a < D + to_Z len) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a))
    /\ (forall j, to_Z i <= j < to_Z len -> exists b, rb segs (ms_mem ms) (S + j) = Some b /\ m' (Z_to_bv 64 (D + j)) = Some b)
    /\ (forall x, ms_mem ms x <> None -> m' x <> None)
    /\ s_pc stn = s_pc st /\ s_rf stn = s_rf st /\ s_ff stn = s_ff st /\ s_resv stn = RNone /\ s_facts stn = s_facts st
    /\ s_ops stn = s_ops st /\ s_priv stn = s_priv st /\ s_next stn = s_next st.
Proof.
  induction fuel as [|fuel IH]; intros i src dst sofs dofs len st stn E ms mo HS RV MRV H Hi S D NWD NWS DISJ.
  - cbn [copy_bytes] in H. destruct (PrimInt63.leb len i) eqn:L; [|discriminate H]. injection H as <-.
    apply Uint63.leb_spec in L. exists (ms_mem ms).
    split; [exact (MemsetFX.st_ok_self segs OPS E st ms mo HS)|].
    split; [intros; reflexivity|]. split; [intros j Hj; lia|]. split; [intros x Hx; exact Hx|]. repeat split; try reflexivity. exact RV.
  - cbn [copy_bytes] in H. destruct (PrimInt63.leb len i) eqn:L.
    + injection H as <-. apply Uint63.leb_spec in L. exists (ms_mem ms).
      split; [exact (MemsetFX.st_ok_self segs OPS E st ms mo HS)|].
      split; [intros; reflexivity|]. split; [intros j Hj; lia|]. split; [intros x Hx; exact Hx|]. repeat split; try reflexivity. exact RV.
    + assert (LT : to_Z i < to_Z len) by (destruct (Uint63.lebP len i) as [Q|Q]; [discriminate L| lia]).
      pose proof (int_range i) as Ri. pose proof (int_range len) as Rl. rewrite two63_eq in Ri, Rl.
      assert (SUBE : to_Z (PrimInt63.sub len i) = to_Z len - to_Z i) by (rewrite Uint63.sub_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
      set (w8 := (PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land (PrimInt63.add sofs i) 7%uint63) 0%uint63
                  && PrimInt63.eqb (PrimInt63.land (PrimInt63.add dofs i) 7%uint63) 0%uint63)%bool) in H.
      set (asrc := sv_alu ALU_ADD src (VL (wlit i))) in H. set (a := sv_alu ALU_ADD dst (VL (wlit i))) in H.
      assert (W8 : w8 = true -> 8 <= to_Z len - to_Z i).
      { intros Q. unfold w8 in Q. apply andb_prop in Q as [Q _]. apply andb_prop in Q as [Q _]. apply Uint63.leb_spec in Q. rewrite SUBE in Q.
        change (to_Z 8%uint63) with 8 in Q. exact Q. }
      set (w := if w8 then 8%uint63 else 1%uint63) in H.
      assert (WZ : to_Z w = if w8 then 8 else 1) by (unfold w; destruct w8; reflexivity).
      assert (W18 : to_Z w = 1 \/ to_Z w = 8) by (rewrite WZ; destruct w8; auto).
      pose proof (bv_unsigned_in_range _ (den E dst)) as RD. unfold bv_modulus in RD. fold D in RD.
      pose proof (bv_unsigned_in_range _ (den E src)) as RS. unfold bv_modulus in RS. fold S in RS.
      assert (DA : den E a = Z_to_bv 64 (D + to_Z i)).
      { unfold a. rewrite MemsetFX.den_add_lit. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. fold D.
        rewrite (bv_wrap_small 64 (to_Z i)) by (unfold bv_modulus; lia). reflexivity. }
      assert (DSa : den E asrc = Z_to_bv 64 (S + to_Z i)).
      { unfold asrc. rewrite MemsetFX.den_add_lit. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. fold S.
        rewrite (bv_wrap_small 64 (to_Z i)) by (unfold bv_modulus; lia). reflexivity. }
      assert (WLE : to_Z i + to_Z w <= to_Z len) by (rewrite WZ; destruct w8 eqn:Q; [specialize (W8 eq_refl); lia| lia]).

      assert (STEP : forall (w0 : int) st1, 1 <= to_Z w0 -> to_Z i + to_Z w0 <= to_Z len ->
                TolFX.piece_ok segs OPS E ms mo st st1 (S + to_Z i) (D + to_Z i) (to_Z w0) ->
                copy_bytes segs fuel (PrimInt63.add i w0) src dst sofs dofs len st1 = Some stn ->
                TolFX.copied segs OPS E ms mo st stn S D (to_Z i) (to_Z len)).
      { intros w0 st1 W0 WL0 PO H1.
        assert (IW : to_Z (PrimInt63.add i w0) = to_Z i + to_Z w0).
        { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
        pose proof PO as (_ & _ & _ & _ & _ & _ & _ & P4 & _).
        apply (TolFX.piece_compose segs OPS E ms mo st st1 stn S D (to_Z i) (to_Z w0) (to_Z len) PO W0 ltac:(lia) WL0 ltac:(lia) ltac:(lia) NWD NWS DISJ).
        intros bs ST.
        pose proof (IH (PrimInt63.add i w0) src dst sofs dofs len st1 stn E _ mo ST P4 MRV H1 ltac:(rewrite IW; lia) NWD NWS DISJ) as R.
        cbv zeta in R. rewrite IW in R. exact R. }
      change (TolFX.copied segs OPS E ms mo st stn S D (to_Z i) (to_Z len)).

      assert (TOL : match (if w8 then do_load segs st asrc 1%uint63 false else inl None) with
                    | inl (Some v1) =>
                        match do_store segs st a 1%uint63 v1 with
                        | inl st' => copy_bytes segs fuel (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
                        | inr _ => None
                        end
                    | _ =>
                        match TolC.skip_byte segs st asrc a with
                        | Some st' => copy_bytes segs fuel (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
                        | None => None
                        end
                    end = Some stn -> TolFX.copied segs OPS E ms mo st stn S D (to_Z i) (to_Z len)).
      { intros HT.
        assert (SKIP : match TolC.skip_byte segs st asrc a with
                       | Some st' => copy_bytes segs fuel (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
                       | None => None
                       end = Some stn -> TolFX.copied segs OPS E ms mo st stn S D (to_Z i) (to_Z len)).
        { intros HK. destruct (TolC.skip_byte segs st asrc a) as [st'|] eqn:SK; [|discriminate HK].
          apply (STEP 1%uint63 st'); [change (to_Z 1%uint63) with 1; lia | change (to_Z 1%uint63) with 1; lia | | exact HK].
          change (to_Z 1%uint63) with 1.
          apply (TolFX.skip_piece segs OPS E st ms mo asrc a st' _ _ HS RV MRV SK DSa DA); unfold two64 in *; lia. }
        destruct (if w8 then do_load segs st asrc 1%uint63 false else inl None) as [[v1|]|] eqn:DL1; [| exact (SKIP HT) | exact (SKIP HT)].
        destruct w8 eqn:Q8; [| discriminate DL1].
        destruct (do_store segs st a 1%uint63 v1) as [st'|] eqn:DS1; [|discriminate HT].
        apply (STEP 1%uint63 st'); [change (to_Z 1%uint63) with 1; lia | change (to_Z 1%uint63) with 1; lia | | exact HT].
        apply (TolFX.load_store_piece segs OPS E st ms mo asrc a 1%uint63 v1 st' _ _ HS RV MRV ltac:(left; reflexivity) DL1 DS1 DSa DA);
          change (to_Z 1%uint63) with 1; unfold two64 in *; lia. }
      destruct (do_load segs st asrc w false) as [[v|]|] eqn:DL; [| exact (TOL H) | exact (TOL H)].
      destruct (do_store segs st a w v) as [st'|] eqn:DS; [|discriminate H].
      apply (STEP w st'); [destruct W18; lia | exact WLE | | exact H].
      apply (TolFX.load_store_piece segs OPS E st ms mo asrc a w v st' _ _ HS RV MRV W18 DL DS DSa DA); unfold two64 in *; lia.
Qed.
End WithSegs.
End MemcpyFX.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import MemcpyC.TwinB MemOps.TwinB MemsetFX.TwinB TolC.TwinB TolFX.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib MemcpyC.TwinB.MemcpyC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module MemcpyFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Definition ov_read_bytes_inv := TolFX.TwinB.TolFX.ov_read_bytes_inv segs.
Definition stored_is_loaded := TolFX.TwinB.TolFX.stored_is_loaded.

Lemma copy_bytes_sound : forall fuel i src dst sofs dofs len st stn E ms mo,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  copy_bytes segs fuel i src dst sofs dofs len st = Some stn ->
  to_Z i <= to_Z len <= 4096 ->
  let S := bv_unsigned (den E src) in let D := bv_unsigned (den E dst) in
  D + to_Z len < two64 -> S + to_Z len < two64 -> (S + to_Z len <= D \/ D + to_Z len <= S) ->
  exists m', St.st_ok segs OPS E stn (ms_with_mem ms m') mo
    /\ (forall a, 0 <= a < two64 -> ~ (D + to_Z i <= a < D + to_Z len) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a))
    /\ (forall j, to_Z i <= j < to_Z len -> exists b, rb segs (ms_mem ms) (S + j) = Some b /\ m' (Z_to_bv 64 (D + j)) = Some b)
    /\ (forall x, ms_mem ms x <> None -> m' x <> None)
    /\ s_pc stn = s_pc st /\ s_rf stn = s_rf st /\ s_ff stn = s_ff st /\ s_resv stn = RNone /\ s_facts stn = s_facts st
    /\ s_ops stn = s_ops st /\ s_priv stn = s_priv st /\ s_next stn = s_next st.
Proof.
  induction fuel as [|fuel IH]; intros i src dst sofs dofs len st stn E ms mo HS RV MRV H Hi S D NWD NWS DISJ.
  - cbn [copy_bytes] in H. destruct (PrimInt63.leb len i) eqn:L; [|discriminate H]. injection H as <-.
    apply Uint63.leb_spec in L. exists (ms_mem ms).
    split; [exact (MemsetFX.TwinB.MemsetFX.st_ok_self segs OPS E st ms mo HS)|].
    split; [intros; reflexivity|]. split; [intros j Hj; lia|]. split; [intros x Hx; exact Hx|]. repeat split; try reflexivity. exact RV.
  - cbn [copy_bytes] in H. destruct (PrimInt63.leb len i) eqn:L.
    + injection H as <-. apply Uint63.leb_spec in L. exists (ms_mem ms).
      split; [exact (MemsetFX.TwinB.MemsetFX.st_ok_self segs OPS E st ms mo HS)|].
      split; [intros; reflexivity|]. split; [intros j Hj; lia|]. split; [intros x Hx; exact Hx|]. repeat split; try reflexivity. exact RV.
    + assert (LT : to_Z i < to_Z len) by (destruct (Uint63.lebP len i) as [Q|Q]; [discriminate L| lia]).
      pose proof (int_range i) as Ri. pose proof (int_range len) as Rl. rewrite two63_eq in Ri, Rl.
      assert (SUBE : to_Z (PrimInt63.sub len i) = to_Z len - to_Z i) by (rewrite Uint63.sub_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
      set (w8 := (PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land (PrimInt63.add sofs i) 7%uint63) 0%uint63
                  && PrimInt63.eqb (PrimInt63.land (PrimInt63.add dofs i) 7%uint63) 0%uint63)%bool) in H.
      set (asrc := sv_alu ALU_ADD src (VL (wlit i))) in H. set (a := sv_alu ALU_ADD dst (VL (wlit i))) in H.
      assert (W8 : w8 = true -> 8 <= to_Z len - to_Z i).
      { intros Q. unfold w8 in Q. apply andb_prop in Q as [Q _]. apply andb_prop in Q as [Q _]. apply Uint63.leb_spec in Q. rewrite SUBE in Q.
        change (to_Z 8%uint63) with 8 in Q. exact Q. }
      set (w := if w8 then 8%uint63 else 1%uint63) in H.
      assert (WZ : to_Z w = if w8 then 8 else 1) by (unfold w; destruct w8; reflexivity).
      assert (W18 : to_Z w = 1 \/ to_Z w = 8) by (rewrite WZ; destruct w8; auto).
      pose proof (bv_unsigned_in_range _ (den E dst)) as RD. unfold bv_modulus in RD. fold D in RD.
      pose proof (bv_unsigned_in_range _ (den E src)) as RS. unfold bv_modulus in RS. fold S in RS.
      assert (DA : den E a = Z_to_bv 64 (D + to_Z i)).
      { unfold a. rewrite MemsetFX.TwinB.MemsetFX.den_add_lit. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. fold D.
        rewrite (bv_wrap_small 64 (to_Z i)) by (unfold bv_modulus; lia). reflexivity. }
      assert (DSa : den E asrc = Z_to_bv 64 (S + to_Z i)).
      { unfold asrc. rewrite MemsetFX.TwinB.MemsetFX.den_add_lit. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. fold S.
        rewrite (bv_wrap_small 64 (to_Z i)) by (unfold bv_modulus; lia). reflexivity. }
      assert (WLE : to_Z i + to_Z w <= to_Z len) by (rewrite WZ; destruct w8 eqn:Q; [specialize (W8 eq_refl); lia| lia]).

      assert (STEP : forall (w0 : int) st1, 1 <= to_Z w0 -> to_Z i + to_Z w0 <= to_Z len ->
                TolFX.TwinB.TolFX.piece_ok segs OPS E ms mo st st1 (S + to_Z i) (D + to_Z i) (to_Z w0) ->
                copy_bytes segs fuel (PrimInt63.add i w0) src dst sofs dofs len st1 = Some stn ->
                TolFX.TwinB.TolFX.copied segs OPS E ms mo st stn S D (to_Z i) (to_Z len)).
      { intros w0 st1 W0 WL0 PO H1.
        assert (IW : to_Z (PrimInt63.add i w0) = to_Z i + to_Z w0).
        { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
        pose proof PO as (_ & _ & _ & _ & _ & _ & _ & P4 & _).
        apply (TolFX.TwinB.TolFX.piece_compose segs OPS E ms mo st st1 stn S D (to_Z i) (to_Z w0) (to_Z len) PO W0 ltac:(lia) WL0 ltac:(lia) ltac:(lia) NWD NWS DISJ).
        intros bs ST.
        pose proof (IH (PrimInt63.add i w0) src dst sofs dofs len st1 stn E _ mo ST P4 MRV H1 ltac:(rewrite IW; lia) NWD NWS DISJ) as R.
        cbv zeta in R. rewrite IW in R. exact R. }
      change (TolFX.TwinB.TolFX.copied segs OPS E ms mo st stn S D (to_Z i) (to_Z len)).

      assert (TOL : match (if w8 then do_load segs st asrc 1%uint63 false else inl None) with
                    | inl (Some v1) =>
                        match do_store segs st a 1%uint63 v1 with
                        | inl st' => copy_bytes segs fuel (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
                        | inr _ => None
                        end
                    | _ =>
                        match TolC.TwinB.TolC.skip_byte segs st asrc a with
                        | Some st' => copy_bytes segs fuel (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
                        | None => None
                        end
                    end = Some stn -> TolFX.TwinB.TolFX.copied segs OPS E ms mo st stn S D (to_Z i) (to_Z len)).
      { intros HT.
        assert (SKIP : match TolC.TwinB.TolC.skip_byte segs st asrc a with
                       | Some st' => copy_bytes segs fuel (PrimInt63.add i 1%uint63) src dst sofs dofs len st'
                       | None => None
                       end = Some stn -> TolFX.TwinB.TolFX.copied segs OPS E ms mo st stn S D (to_Z i) (to_Z len)).
        { intros HK. destruct (TolC.TwinB.TolC.skip_byte segs st asrc a) as [st'|] eqn:SK; [|discriminate HK].
          apply (STEP 1%uint63 st'); [change (to_Z 1%uint63) with 1; lia | change (to_Z 1%uint63) with 1; lia | | exact HK].
          change (to_Z 1%uint63) with 1.
          apply (TolFX.TwinB.TolFX.skip_piece segs OPS E st ms mo asrc a st' _ _ HS RV MRV SK DSa DA); unfold two64 in *; lia. }
        destruct (if w8 then do_load segs st asrc 1%uint63 false else inl None) as [[v1|]|] eqn:DL1; [| exact (SKIP HT) | exact (SKIP HT)].
        destruct w8 eqn:Q8; [| discriminate DL1].
        destruct (do_store segs st a 1%uint63 v1) as [st'|] eqn:DS1; [|discriminate HT].
        apply (STEP 1%uint63 st'); [change (to_Z 1%uint63) with 1; lia | change (to_Z 1%uint63) with 1; lia | | exact HT].
        apply (TolFX.TwinB.TolFX.load_store_piece segs OPS E st ms mo asrc a 1%uint63 v1 st' _ _ HS RV MRV ltac:(left; reflexivity) DL1 DS1 DSa DA);
          change (to_Z 1%uint63) with 1; unfold two64 in *; lia. }
      destruct (do_load segs st asrc w false) as [[v|]|] eqn:DL; [| exact (TOL H) | exact (TOL H)].
      destruct (do_store segs st a w v) as [st'|] eqn:DS; [|discriminate H].
      apply (STEP w st'); [destruct W18; lia | exact WLE | | exact H].
      apply (TolFX.TwinB.TolFX.load_store_piece segs OPS E st ms mo asrc a w v st' _ _ HS RV MRV W18 DL DS DSa DA); unfold two64 in *; lia.
Qed.
End WithSegs.
End MemcpyFX.
End TwinB.
