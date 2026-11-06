(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition F_ATOF : Z := 0xe177c.
(* [comment removed for export] *)
Definition ATOF_STACK : Z := 8832.
(* [comment removed for export] *)
Definition fa0r : bv 5 := Z_to_bv 5 10.

(* [comment removed for export] *)
Definition atof_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (m : mem) (usp lo d : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc None m' (seg_rom asegs)
    /\ reg_get F' fa0r = Z_to_bv 64 d
    /\ munch [(usp - ATOF_STACK, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zclosed e :=
  lazymatch e with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | Z.add ?a ?b => zclosed a; zclosed b
  | Z.sub ?a ?b => zclosed a; zclosed b
  | Z.mul ?a ?b => zclosed a; zclosed b
  | Z.div ?a ?b => zclosed a; zclosed b
  | Z.modulo ?a ?b => zclosed a; zclosed b
  | Z.land ?a ?b => zclosed a; zclosed b
  | Z.lor ?a ?b => zclosed a; zclosed b
  | Z.lxor ?a ?b => zclosed a; zclosed b
  | Z.shiftl ?a ?b => zclosed a; zclosed b
  | Z.shiftr ?a ?b => zclosed a; zclosed b
  | Z.opp ?a => zclosed a
  | Z.b2z ?c => bclosed c
  | bv_swrap _ ?a => zclosed a
  | bv_wrap _ ?a => zclosed a
  | bv_unsigned ?w => wclosed w
  | bv_signed ?w => wclosed w
  end
with wclosed w :=
  lazymatch w with
  | Z_to_bv _ ?e => zclosed e
  | sx32 ?a => wclosed a
  | zx32 ?a => wclosed a
  | sxb ?a => wclosed a
  | zxb ?a => wclosed a
  end
with bclosed c :=
  lazymatch c with
  | true => idtac | false => idtac
  | Z.ltb ?a ?b => zclosed a; zclosed b
  | Z.leb ?a ?b => zclosed a; zclosed b
  | Z.eqb ?a ?b => zclosed a; zclosed b
  | negb ?x => bclosed x
  | andb ?x ?y => bclosed x; bclosed y
  | orb ?x ?y => bclosed x; bclosed y
  end.
Ltac not_Zlit e := lazymatch e with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end.
Ltac is_wlit w := lazymatch w with Z_to_bv 64 ?e => is_Zlit e end.
(* [comment removed for export] *)
Ltac fold_closed_regs :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with context [Some ?w] =>
        tryif is_wlit w then fail else idtac;
        wclosed w;
        let v := eval vm_compute in (bv_unsigned w) in
        replace w with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
      end
  end.
(* [comment removed for export] *)
Ltac fold_closed :=
  repeat match goal with
  | |- context [Z.b2z ?c] => bclosed c; let v := eval vm_compute in (Z.b2z c) in change (Z.b2z c) with v
  | |- context [Z_to_bv 64 ?e] => not_Zlit e; zclosed e; let v := eval vm_compute in (e mod 18446744073709551616) in
        replace (Z_to_bv 64 e) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
  | |- context [bv_swrap ?n ?a] => zclosed a; let v := eval vm_compute in (bv_swrap n a) in
        replace (bv_swrap n a) with v by (vm_compute; reflexivity)
  | |- context [Z.modulo ?a ?b] => not_Zlit a; zclosed a; zclosed b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
  | |- context [Z.mul ?a ?b] => zclosed a; zclosed b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  | |- context [Z.land Z0 ?x] => rewrite (Z.land_0_l x)
  | |- context [Z.land ?x Z0] => rewrite (Z.land_0_r x)
  | |- context [Z.add ?x Z0] => rewrite (Z.add_0_r x)
  end.
(* [comment removed for export] *)
Ltac cwalk1 := lwalk1; try fold_closed_regs; try fold_closed.
Ltac cwalk stops := repeat (tryif at_stop stops then fail else cwalk1).
(* [comment removed for export] *)
Ltac tok_read i b :=
  lazymatch goal with TOKx : bytes_at asegs ?mc ?s ?bs |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let RD := fresh "RD" in
    first [ pose proof (u8ro_read asegs mc s bs i b (Z_to_bv 64 (s + i)) TOKx eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD; lstep
          | pose proof (u8ro_read asegs mc s bs i b (Z_to_bv 64 s) TOKx eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD; lstep ];
    clear RD; try fold_closed_regs; try fold_closed end.
(* [comment removed for export] *)
Ltac rel_at A hi := lazymatch goal with FRx : rw_cells asegs _ A _, STx : stk asegs _ _ A |- _ => release_frame FRx STx hi end.
(* [comment removed for export] *)
Ltac atof_finish usp MU WM MI :=
  rel_at (usp + -8688) (usp + -8448); rel_at (usp + -8448) (usp + -6400); rel_at (usp + -6400) (usp + -2304);
  rel_at (usp + -2304) (usp + -272); rel_at (usp + -272) usp;
  apply evt_done; unfold atof_post;
  lazymatch goal with |- exists _, _ => idtac end;
  do 15 eexists;
  lazymatch goal with |- exists F' m', MS _ ?Fx _ _ _ ?mx _ = _ /\ _ => exists Fx, mx end;
  split; [ norm_regset; reflexivity | ];
  split; [ unfold fa0r; rewrite freg_get_other by reflexivity; apply freg_get_same; reflexivity | ];
  split; [ exact MU | ]; split; [ exact WM | ]; split; [ exact MI | ];
  lazymatch goal with STx : stk asegs _ _ usp |- _ => exact STx end.
