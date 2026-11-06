(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

(* [comment removed for export] *)
Ltac rd1x A bs HB :=
  next_instr ltac:(fun i => lazymatch i with
    | Load SZ1 _ _ ?rs _ => reg_val rs ltac:(fun v => lazymatch v with
        | Z_to_bv 64 (Z.lxor ?X 3) =>
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
              let b := fresh "dv" in let R := fresh "RD" in let LX := fresh "LXr" in
              pose proof (lxor3_eq X) as LX;
              destruct (bytes_at_read1 m A bs (Z.lxor X 3 - A) HB ltac:(lia)) as (b & R);
              replace (A + (Z.lxor X 3 - A)) with (Z.lxor X 3) in R by lia; lstep; clear R LX end
        end)
    end).

(* [comment removed for export] *)
Ltac diam :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?T else Z_to_bv 64 ?N) ?fc ?rv ?m ?ro) =>
      let ok := eval vm_compute in (Z.eqb T (N + 4)) in
      lazymatch ok with true => idtac end;
      instr_at segs N ltac:(fun i => lazymatch i with
        | OpImm ALU_ADD ?rd _ _ =>
            eapply (evt_cut segs (fun ms' => exists u' : word, ms' = MS (@bvmap_set 5 word rd u' R) F (Z_to_bv 64 T) fc rv m ro));
            [ let H := fresh "DC" in if_cases H;
              [ apply evt_done;
                lazymatch goal with |- exists u', _ = MS (@bvmap_set 5 word ?r u' ?R') _ _ _ _ _ _ =>
                  let p := eval vm_compute in (bv_key r) in
                  let v := eval cbv beta iota delta [tget mkR] in (tget p R') in
                  lazymatch v with Some ?x => exists x end end;
                norm_regset; reflexivity
              | lstep; apply evt_done; eexists; norm_regset; reflexivity ]
            | let u' := fresh "mv" in let ms := fresh "ms" in let E := fresh "E" in intros ms (u' & E); subst ms; norm_regset ]
        end)
  end.

(* [comment removed for export] *)
Ltac arr_sbx A :=
  next_instr ltac:(fun i => lazymatch i with
    | Store SZ1 ?rs1 _ _ => reg_val rs1 ltac:(fun v => lazymatch v with
        | Z_to_bv 64 (Z.lxor ?X 3) =>
            lazymatch goal with
            | UA : u8arr asegs ?mm A ?bs, UAL : Z.of_nat (length ?bs) = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
                let SOK := fresh "SOK" in let LX := fresh "LXs" in let idx := fresh "idx" in let Eidx := fresh "Eidx" in
                pose proof (lxor3_eq X) as LX;
                remember (Z.lxor X 3 - A) as idx eqn:Eidx;
                pose proof (u8arr_store_ok asegs mm A bs idx (wa (Z.lxor X 3)) UA ltac:(lia) ltac:(f_equal; lia)) as SOK;
                zstep;
                lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm (Z_to_bv 64 ?E') (le1 ?sv)) _) =>
                  let N := fresh "UA" in
                  rewrite (le1_byte sv);
                  assert (N : u8arr asegs (write_to_mem mm (wa E') [Z_to_bv 8 (bv_unsigned sv)]) A (upd bs (Z.to_nat idx) (Z_to_bv 8 (bv_unsigned sv))))
                    by (replace (wa E') with (wa (A + idx)) by (f_equal; lia); apply (u8arr_write asegs mm A bs idx _ UA); lia);
                  clear UA; store_done; rename N into UA;
                  rewrite <- (upd_length bs (Z.to_nat idx) (Z_to_bv 8 (bv_unsigned sv))) in UAL;
                  let bs' := fresh "abs" in set (bs' := upd bs (Z.to_nat idx) (Z_to_bv 8 (bv_unsigned sv))) in *; clearbody bs'; try clear bs;
                  clear LX Eidx; try clear idx
                end
            end
        end)
    end).

(* [comment removed for export] *)
Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

(* [comment removed for export] *)
Ltac k3h1 As bss HB Ad :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ diam | shbr_x3 | shbr | br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
      first [ shload; lstep; clear_shl | unhide_all; arr_sbx Ad; hide_disj | rd1x As bss HB | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
Ltac k3hwalk As bss HB Ad stops := repeat (tryif at_stop stops then fail else k3h1 As bss HB Ad).
