(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcdefs.
Module ICPT_pcdefs2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Lemma lowsh_word8 : forall m base, lowsh_at m -> SH AIMG_LO <= base -> base + 8 <= SH AIMG_HI ->
  rw_cells asegs m base [C1 (zb (alowsh base)); C1 (zb (alowsh (base + 1))); C1 (zb (alowsh (base + 2))); C1 (zb (alowsh (base + 3)));
                         C1 (zb (alowsh (base + 4))); C1 (zb (alowsh (base + 5))); C1 (zb (alowsh (base + 6))); C1 (zb (alowsh (base + 7)))].
Proof.
  intros m base L H1 H2.
  assert (G : forall k, 0 <= k < 8 -> rw_cells asegs m (base + k) [C1 (zb (alowsh (base + k)))]).
  { intros k Hk. apply L. lia. }
  Ltac glue1 H1 H2 := let X := fresh in pose proof (proj2 (rw_cells_app asegs _ _ _ _) (conj H1 H2)) as X; clear H1 H2; rename X into H1; cbn [app cells_size csize Nat.add Z.of_nat] in H1.
  pose proof (G 0 ltac:(lia)) as G0. rewrite !Z.add_0_r in G0.
  pose proof (G 1 ltac:(lia)) as G1. replace (base + 1) with (base + Z.of_nat (cells_size [C1 (zb (alowsh base))])) in G1 at 1 by (cbn; lia). glue1 G0 G1.
  pose proof (G 2 ltac:(lia)) as G2. replace (base + 2) with (base + Z.of_nat (cells_size [C1 (zb (alowsh base)); C1 (zb (alowsh (base + 1)))])) in G2 at 1 by (cbn; lia). glue1 G0 G2.
  pose proof (G 3 ltac:(lia)) as G3. replace (base + 3) with (base + Z.of_nat (cells_size [C1 (zb (alowsh base)); C1 (zb (alowsh (base + 1))); C1 (zb (alowsh (base + 2)))])) in G3 at 1 by (cbn; lia). glue1 G0 G3.
  pose proof (G 4 ltac:(lia)) as G4. replace (base + 4) with (base + Z.of_nat (cells_size [C1 (zb (alowsh base)); C1 (zb (alowsh (base + 1))); C1 (zb (alowsh (base + 2))); C1 (zb (alowsh (base + 3)))])) in G4 at 1 by (cbn; lia). glue1 G0 G4.
  pose proof (G 5 ltac:(lia)) as G5. replace (base + 5) with (base + Z.of_nat (cells_size [C1 (zb (alowsh base)); C1 (zb (alowsh (base + 1))); C1 (zb (alowsh (base + 2))); C1 (zb (alowsh (base + 3))); C1 (zb (alowsh (base + 4)))])) in G5 at 1 by (cbn; lia). glue1 G0 G5.
  pose proof (G 6 ltac:(lia)) as G6. replace (base + 6) with (base + Z.of_nat (cells_size [C1 (zb (alowsh base)); C1 (zb (alowsh (base + 1))); C1 (zb (alowsh (base + 2))); C1 (zb (alowsh (base + 3))); C1 (zb (alowsh (base + 4))); C1 (zb (alowsh (base + 5)))])) in G6 at 1 by (cbn; lia). glue1 G0 G6.
  pose proof (G 7 ltac:(lia)) as G7. replace (base + 7) with (base + Z.of_nat (cells_size [C1 (zb (alowsh base)); C1 (zb (alowsh (base + 1))); C1 (zb (alowsh (base + 2))); C1 (zb (alowsh (base + 3))); C1 (zb (alowsh (base + 4))); C1 (zb (alowsh (base + 5))); C1 (zb (alowsh (base + 6)))])) in G7 at 1 by (cbn; lia). glue1 G0 G7.
  exact G0.
Qed.
(* [comment removed for export] *)
Ltac lowsh_eval H :=
  repeat match type of H with context [alowsh ?a] => let v := eval vm_compute in (alowsh a) in change (alowsh a) with v in H end;
  repeat match type of H with context [Z.add ?a ?b] =>
    lazymatch a with Zpos _ => lazymatch b with Zpos _ => let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H end end end.

(* [comment removed for export] *)
Lemma fmt_dn_bytes : forall m, mem_inv asegs m -> ro_cells asegs m 0x1484b [CB 4 (zbs [37; 100; 10; 0])].
Proof. intros m MI. apply (ro_cells_image asegs m 0x1484b (zbs [37; 100; 10; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac at_any3 p1 p2 p3 :=
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => first [constr_eq q p1 | constr_eq q p2 | constr_eq q p3] end.
Ltac gsto3 p1 p2 p3 := repeat (tryif at_any3 p1 p2 p3 then fail else lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => gs end).
(* [comment removed for export] *)
Ltac pc_dir5 :=
  lazymatch goal with FBd : rw_cells asegs ?mm (bv_unsigned ?u + -2216) ?cs |- _ =>
    lazymatch cs with
    | [_; _; _; _; _] => idtac
    | _ => apply (rw_cells_recast asegs mm (bv_unsigned u + -2216) cs
                   [CB 8 (firstn 8 (cells_bytes cs)); CB 8 (firstn 8 (skipn 8 (cells_bytes cs))); CB 8 (firstn 8 (skipn 16 (cells_bytes cs)));
                    CB 8 (firstn 8 (skipn 24 (cells_bytes cs))); CB 8 (firstn 8 (skipn 32 (cells_bytes cs)))]) in FBd;
           [ cbn [cells_bytes cbytes app firstn skipn le8 le4] in FBd
           | cbn; repeat split; try exact I; reflexivity
           | apply bytes_eqb_sound; vm_compute; reflexivity ]
    end end.
(* [comment removed for export] *)
Ltac pc_iter :=
  pc_dir5;
  gsto 0x461c4%Z; gs;
  lazymatch goal with FBd : rw_cells asegs _ (bv_unsigned ?u + -2216) _ |- _ =>
    apply (rw_cells_merge asegs _ _ [] [_; _; _; _; _] []) in FBd; cbn [cells_size csize cells_bytes cbytes app Nat.add] in FBd;
    call imemset_call;
    [ exact FBd | assumption | lia | lia | lia | lia
    | intros E; rewrite Z.land_lor_distr_l in E; apply Z.lor_eq_0_iff in E; destruct E as [E _]; vm_compute in E; lia | ]
  end;
  lazymatch goal with FBd : rw_cells asegs _ (bv_unsigned ?u + -2216) [CB _ (repeat _ _)] |- _ =>
    change (0 mod 256) with 0 in FBd; change (Z.to_nat 40) with 40%nat in FBd; cbn [repeat] in FBd;
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [4; 4; 8; 8; 8; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FBd; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FBd
  end;
  gs;   (* [comment removed for export] *)
  lazymatch goal with FBd : rw_cells asegs ?mm (bv_unsigned ?u + -2216) [?c0; ?c1; C8 ?v; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12] |- _ =>
    apply (rw_cells_recast asegs mm (bv_unsigned u + -2216) _ [c0; c1; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); c3; c4; c5; c6; c7; c8; c9; c10; c11; c12]) in FBd;
    [| cbn; repeat split; exact I | apply bytes_eqb_sound; vm_compute; reflexivity] end;
  gsto3 0x495c0%Z 0x461a0%Z 0x46978%Z;
  try (at_pc 0x495c0%Z;
       lazymatch goal with STa : stk asegs _ _ (bv_unsigned ?u + -2240) |- _ =>
         carve_frame 32%nat STa;
         lazymatch goal with FV : rw_cells asegs _ (bv_unsigned u + -2272) _ |- _ =>
           apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8]%nat) in FV; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FV end;
         gsto 0x46418%Z;
         lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           lazymatch goal with H : rw_cells asegs mm (bv_unsigned u + -2272) _ |- _ =>
             lazymatch goal with STa' : stk asegs mm _ (bv_unsigned u + -2272) |- _ =>
               release_frame H STa' (bv_unsigned u + -2240) end end end end;
       gsto3 0x495c0%Z 0x461a0%Z 0x46978%Z).
(* [comment removed for export] *)
Ltac pc_walk :=
  do 16 gs;
  gsto 0x46124%Z;
  lazymatch goal with SHW : rw_cells asegs _ _ [C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _] |- _ => shw_read SHW end;
  gs; gs;
  repeat match goal with RD : ov_read_bytes _ _ _ _ = Some _ |- _ => clear RD end;
  gsto3 0x461a0%Z 0x46978%Z 0x46978%Z;
  repeat (at_pc 0x461a0%Z; pc_iter);
  repeat gs;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch goal with STa : stk asegs mm _ (bv_unsigned ?u + -2240) |- _ =>
  lazymatch goal with STb : stk asegs mm (bv_unsigned u + -2176) _ |- _ =>
  lazymatch goal with FBa : rw_cells asegs mm (bv_unsigned u + -2240) _ |- _ =>
  lazymatch goal with FBd : rw_cells asegs mm (bv_unsigned u + -2216) _ |- _ =>
  lazymatch goal with FR : rw_cells asegs mm (bv_unsigned u + -104) _ |- _ =>
    release_frame FBa STa (bv_unsigned u + -2216);
    release_frame FBd STa (bv_unsigned u + -2176);
    let ST := fresh "ST" in
    pose proof (stk_merge asegs mm _ _ _ STa STb ltac:(lia)) as ST; clear STa STb;
    release_frame FR ST (bv_unsigned u) end end end end end end;
  finish.


End CeilWrap.
(* [comment removed for export] *)
Ltac lowsh_eval H :=
  repeat match type of H with context [alowsh ?a] => let v := eval vm_compute in (alowsh a) in change (alowsh a) with v in H end;
  repeat match type of H with context [Z.add ?a ?b] =>
    lazymatch a with Zpos _ => lazymatch b with Zpos _ => let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H end end end.
Ltac at_any3 p1 p2 p3 :=
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => first [constr_eq q p1 | constr_eq q p2 | constr_eq q p3] end.
Ltac gsto3 p1 p2 p3 := repeat (tryif at_any3 p1 p2 p3 then fail else lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => gs end).
Ltac pc_dir5 :=
  lazymatch goal with FBd : rw_cells asegs ?mm (bv_unsigned ?u + -2216) ?cs |- _ =>
    lazymatch cs with
    | [_; _; _; _; _] => idtac
    | _ => apply (rw_cells_recast asegs mm (bv_unsigned u + -2216) cs
                   [CB 8 (firstn 8 (cells_bytes cs)); CB 8 (firstn 8 (skipn 8 (cells_bytes cs))); CB 8 (firstn 8 (skipn 16 (cells_bytes cs)));
                    CB 8 (firstn 8 (skipn 24 (cells_bytes cs))); CB 8 (firstn 8 (skipn 32 (cells_bytes cs)))]) in FBd;
           [ cbn [cells_bytes cbytes app firstn skipn le8 le4] in FBd
           | cbn; repeat split; try exact I; reflexivity
           | apply bytes_eqb_sound; vm_compute; reflexivity ]
    end end.
Ltac pc_iter :=
  pc_dir5;
  gsto 0x461c4%Z; gs;
  lazymatch goal with FBd : rw_cells asegs _ (bv_unsigned ?u + -2216) _ |- _ =>
    apply (rw_cells_merge asegs _ _ [] [_; _; _; _; _] []) in FBd; cbn [cells_size csize cells_bytes cbytes app Nat.add] in FBd;
    call imemset_call;
    [ exact FBd | assumption | lia | lia | lia | lia
    | intros E; rewrite Z.land_lor_distr_l in E; apply Z.lor_eq_0_iff in E; destruct E as [E _]; vm_compute in E; lia | ]
  end;
  lazymatch goal with FBd : rw_cells asegs _ (bv_unsigned ?u + -2216) [CB _ (repeat _ _)] |- _ =>
    change (0 mod 256) with 0 in FBd; change (Z.to_nat 40) with 40%nat in FBd; cbn [repeat] in FBd;
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [4; 4; 8; 8; 8; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FBd; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FBd
  end;
  gs;   
  lazymatch goal with FBd : rw_cells asegs ?mm (bv_unsigned ?u + -2216) [?c0; ?c1; C8 ?v; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12] |- _ =>
    apply (rw_cells_recast asegs mm (bv_unsigned u + -2216) _ [c0; c1; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); c3; c4; c5; c6; c7; c8; c9; c10; c11; c12]) in FBd;
    [| cbn; repeat split; exact I | apply bytes_eqb_sound; vm_compute; reflexivity] end;
  gsto3 0x495c0%Z 0x461a0%Z 0x46978%Z;
  try (at_pc 0x495c0%Z;
       lazymatch goal with STa : stk asegs _ _ (bv_unsigned ?u + -2240) |- _ =>
         carve_frame 32%nat STa;
         lazymatch goal with FV : rw_cells asegs _ (bv_unsigned u + -2272) _ |- _ =>
           apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8]%nat) in FV; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FV end;
         gsto 0x46418%Z;
         lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           lazymatch goal with H : rw_cells asegs mm (bv_unsigned u + -2272) _ |- _ =>
             lazymatch goal with STa' : stk asegs mm _ (bv_unsigned u + -2272) |- _ =>
               release_frame H STa' (bv_unsigned u + -2240) end end end end;
       gsto3 0x495c0%Z 0x461a0%Z 0x46978%Z).
Ltac pc_walk :=
  do 16 gs;
  gsto 0x46124%Z;
  lazymatch goal with SHW : rw_cells asegs _ _ [C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _; C1 _] |- _ => shw_read SHW end;
  gs; gs;
  repeat match goal with RD : ov_read_bytes _ _ _ _ = Some _ |- _ => clear RD end;
  gsto3 0x461a0%Z 0x46978%Z 0x46978%Z;
  repeat (at_pc 0x461a0%Z; pc_iter);
  repeat gs;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch goal with STa : stk asegs mm _ (bv_unsigned ?u + -2240) |- _ =>
  lazymatch goal with STb : stk asegs mm (bv_unsigned u + -2176) _ |- _ =>
  lazymatch goal with FBa : rw_cells asegs mm (bv_unsigned u + -2240) _ |- _ =>
  lazymatch goal with FBd : rw_cells asegs mm (bv_unsigned u + -2216) _ |- _ =>
  lazymatch goal with FR : rw_cells asegs mm (bv_unsigned u + -104) _ |- _ =>
    release_frame FBa STa (bv_unsigned u + -2216);
    release_frame FBd STa (bv_unsigned u + -2176);
    let ST := fresh "ST" in
    pose proof (stk_merge asegs mm _ _ _ STa STb ltac:(lia)) as ST; clear STa STb;
    release_frame FR ST (bv_unsigned u) end end end end end end;
  finish.
End ICPT_pcdefs2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Module ICPT_pcommon_d.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs ICPT_pcdefs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Pcommon_d.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SB : shbase_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APC_STACK <= bv_unsigned sp.

  Lemma pcommon_d_body :
    evt asegs (pcommon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x21220) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APRINTF_COMMON) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold APC_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (tbl_flags m MI) as T1. pose proof (tbl_lenmod m MI) as T2. pose proof (tbl_cs m MI) as T3.
    pose proof (tbl_iconv m MI) as T4. pose proof (tbl_fconv m MI) as T5. pose proof (tbl_aa m MI) as T6. pose proof (tbl_atoll m MI) as T7.
    pose proof (fmt_d_bytes m MI) as FMT.
    pose proof (lowsh_word8 m 0x7fffc240 LOW ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO; lia) ltac:(unfold SH, SHADOW_OFFSET, AIMG_HI; lia)) as SHW. lowsh_eval SHW.
    pose proof SB as SB'. shbase_split SB'.
    unfold APRINTF_COMMON.
    (* [comment removed for export] *)
    pose proof ST0 as ST. clear ST0. carve_frame 104%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (stk_split asegs _ lo (bv_unsigned sp + -2176) (bv_unsigned sp + -104) ST ltac:(lia)) as [STa STb]. clear ST.
    carve_frame 64%nat STa. rename FR0 into FB.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FB. destruct FB as [FBa FBd]. cbn [cells_size csize Nat.add app] in FBd.
    replace (bv_unsigned sp + -2240 + Z.of_nat 24) with (bv_unsigned sp + -2216) in FBd by lia.
    pc_walk.
  Qed.
End Pcommon_d.

Lemma pcommon_d_ok : pcommon_stmt 0x21220.
Proof. unfold pcommon_stmt. intros until lo. intros MI SB LOW ST CEIL SPB ->. eapply pcommon_d_body; eassumption. Qed.


End CeilWrap.
End ICPT_pcommon_d.

(* [comment removed for export] *)
Module ICPT_pcommon_dn.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs ICPT_pcdefs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Pcommon_dn.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SB : shbase_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APC_STACK <= bv_unsigned sp.

  Lemma pcommon_dn_body :
    evt asegs (pcommon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x1484b) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APRINTF_COMMON) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold APC_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (tbl_flags m MI) as T1. pose proof (tbl_lenmod m MI) as T2. pose proof (tbl_cs m MI) as T3.
    pose proof (tbl_iconv m MI) as T4. pose proof (tbl_fconv m MI) as T5. pose proof (tbl_aa m MI) as T6. pose proof (tbl_atoll m MI) as T7.
    pose proof (fmt_dn_bytes m MI) as FMT.
    pose proof (lowsh_word8 m 0x7fffa908 LOW ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO; lia) ltac:(unfold SH, SHADOW_OFFSET, AIMG_HI; lia)) as SHW. lowsh_eval SHW.
    pose proof SB as SB'. shbase_split SB'.
    unfold APRINTF_COMMON.
    (* [comment removed for export] *)
    pose proof ST0 as ST. clear ST0. carve_frame 104%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (stk_split asegs _ lo (bv_unsigned sp + -2176) (bv_unsigned sp + -104) ST ltac:(lia)) as [STa STb]. clear ST.
    carve_frame 64%nat STa. rename FR0 into FB.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FB. destruct FB as [FBa FBd]. cbn [cells_size csize Nat.add app] in FBd.
    replace (bv_unsigned sp + -2240 + Z.of_nat 24) with (bv_unsigned sp + -2216) in FBd by lia.
    pc_walk.
  Qed.
End Pcommon_dn.

Lemma pcommon_dn_ok : pcommon_stmt 0x1484b.
Proof. unfold pcommon_stmt. intros until lo. intros MI SB LOW ST CEIL SPB ->. eapply pcommon_dn_body; eassumption. Qed.


End CeilWrap.
End ICPT_pcommon_dn.

(* [comment removed for export] *)
Module ICPT_pcommon_g15.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs ICPT_pcdefs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Pcommon_g15.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SB : shbase_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APC_STACK <= bv_unsigned sp.

  Lemma pcommon_g15_body :
    evt asegs (pcommon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x21240) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APRINTF_COMMON) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold APC_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (tbl_flags m MI) as T1. pose proof (tbl_lenmod m MI) as T2. pose proof (tbl_cs m MI) as T3.
    pose proof (tbl_iconv m MI) as T4. pose proof (tbl_fconv m MI) as T5. pose proof (tbl_aa m MI) as T6. pose proof (tbl_atoll m MI) as T7.
    pose proof (fmt_g15_bytes m MI) as FMT.
    pose proof (lowsh_word8 m 0x7fffc248 LOW ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO; lia) ltac:(unfold SH, SHADOW_OFFSET, AIMG_HI; lia)) as SHW. lowsh_eval SHW.
    pose proof SB as SB'. shbase_split SB'.
    unfold APRINTF_COMMON.
    (* [comment removed for export] *)
    pose proof ST0 as ST. clear ST0. carve_frame 104%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (stk_split asegs _ lo (bv_unsigned sp + -2176) (bv_unsigned sp + -104) ST ltac:(lia)) as [STa STb]. clear ST.
    carve_frame 64%nat STa. rename FR0 into FB.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FB. destruct FB as [FBa FBd]. cbn [cells_size csize Nat.add app] in FBd.
    replace (bv_unsigned sp + -2240 + Z.of_nat 24) with (bv_unsigned sp + -2216) in FBd by lia.
    pc_walk.
  Qed.
End Pcommon_g15.

Lemma pcommon_g15_ok : pcommon_stmt 0x21240.
Proof. unfold pcommon_stmt. intros until lo. intros MI SB LOW ST CEIL SPB ->. eapply pcommon_g15_body; eassumption. Qed.


End CeilWrap.
End ICPT_pcommon_g15.

(* [comment removed for export] *)
Module ICPT_pcommon_g17.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs ICPT_pcdefs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Pcommon_g17.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SB : shbase_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APC_STACK <= bv_unsigned sp.

  Lemma pcommon_g17_body :
    evt asegs (pcommon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x21280) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APRINTF_COMMON) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold APC_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (tbl_flags m MI) as T1. pose proof (tbl_lenmod m MI) as T2. pose proof (tbl_cs m MI) as T3.
    pose proof (tbl_iconv m MI) as T4. pose proof (tbl_fconv m MI) as T5. pose proof (tbl_aa m MI) as T6. pose proof (tbl_atoll m MI) as T7.
    pose proof (fmt_g17_bytes m MI) as FMT.
    pose proof (lowsh_word8 m 0x7fffc250 LOW ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO; lia) ltac:(unfold SH, SHADOW_OFFSET, AIMG_HI; lia)) as SHW. lowsh_eval SHW.
    pose proof SB as SB'. shbase_split SB'.
    unfold APRINTF_COMMON.
    (* [comment removed for export] *)
    pose proof ST0 as ST. clear ST0. carve_frame 104%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (stk_split asegs _ lo (bv_unsigned sp + -2176) (bv_unsigned sp + -104) ST ltac:(lia)) as [STa STb]. clear ST.
    carve_frame 64%nat STa. rename FR0 into FB.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FB. destruct FB as [FBa FBd]. cbn [cells_size csize Nat.add app] in FBd.
    replace (bv_unsigned sp + -2240 + Z.of_nat 24) with (bv_unsigned sp + -2216) in FBd by lia.
    pc_walk.
  Qed.
End Pcommon_g17.

Lemma pcommon_g17_ok : pcommon_stmt 0x21280.
Proof. unfold pcommon_stmt. intros until lo. intros MI SB LOW ST CEIL SPB ->. eapply pcommon_g17_body; eassumption. Qed.


End CeilWrap.
End ICPT_pcommon_g17.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg ICPT_pcleaf ICPT_pcdefs.
Import ICPT_pcdefs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Pcommon_u04x.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SB : shbase_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APC_STACK <= bv_unsigned sp.

  Lemma pcommon_u04x_body :
    evt asegs (pcommon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x212c0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APRINTF_COMMON) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold APC_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (tbl_flags m MI) as T1. pose proof (tbl_lenmod m MI) as T2. pose proof (tbl_cs m MI) as T3.
    pose proof (tbl_iconv m MI) as T4. pose proof (tbl_fconv m MI) as T5. pose proof (tbl_aa m MI) as T6. pose proof (tbl_atoll m MI) as T7.
    pose proof (fmt_u04x_bytes m MI) as FMT.
    pose proof (lowsh_word8 m 0x7fffc258 LOW ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO; lia) ltac:(unfold SH, SHADOW_OFFSET, AIMG_HI; lia)) as SHW. lowsh_eval SHW.
    pose proof SB as SB'. shbase_split SB'.
    unfold APRINTF_COMMON.
    (* [comment removed for export] *)
    pose proof ST0 as ST. clear ST0. carve_frame 104%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (stk_split asegs _ lo (bv_unsigned sp + -2176) (bv_unsigned sp + -104) ST ltac:(lia)) as [STa STb]. clear ST.
    carve_frame 64%nat STa. rename FR0 into FB.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FB. destruct FB as [FBa FBd]. cbn [cells_size csize Nat.add app] in FBd.
    replace (bv_unsigned sp + -2240 + Z.of_nat 24) with (bv_unsigned sp + -2216) in FBd by lia.
    pc_walk.
  Qed.
End Pcommon_u04x.

Lemma pcommon_u04x_ok : pcommon_stmt 0x212c0.
Proof. unfold pcommon_stmt. intros until lo. intros MI SB LOW ST CEIL SPB ->. eapply pcommon_u04x_body; eassumption. Qed.


End CeilWrap.
