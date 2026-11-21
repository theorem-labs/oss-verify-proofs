(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the walk of musl's __vdsosym at LPS 727298f3 (auxv pair 0, the vDSO ELF header, program headers, dynamic section, hash table, symbol and version tables) to its clock_gettime entry. *)

(* WHAT IS WALKED.  musl 1.2's [__vdsosym(vername, name)] (src/internal/vdso.c), from its
   entry to its return, over the run's segment list [rvsegs tail] = [VW_BSEGS ++ tail]:
     - the auxv scan for AT_SYSINFO_EHDR (33), which is pair 0 at LPS 727298f3;
     - the ELF header and the program headers (PT_LOAD gives the load bias, PT_DYNAMIC the
       dynamic section);
     - the dynamic section (DT_STRTAB, DT_SYMTAB, DT_HASH/DT_GNU_HASH, DT_VERSYM, DT_VERDEF);
     - [count_syms] over the GNU hash table;
     - the symbol loop with its calls to the binary's [strcmp], and [checkver]'s.
   Every byte of the vDSO is read through [Lib/VdsoImg.v]'s [rvdso_read], at the offset the
   instruction's address names, and every branch is decided by proof ([vif]): a condition
   that is not provably true or provably false stops the walk.

   WHAT IS BINARY-SPECIFIC is only [RVdsoAddr.v] of this directory: the binary's segment
   list, the entry, the auxv cell and the two strings.  A binary linked against the same musl
   takes the walk by copying [RVdsoSegs.v], [RVdsoSym.v] and this file next to its own
   [RVdsoAddr.v] and changing the directory in their Require lines.

   THE PREMISES are the ones a caller has at a call of __vdsosym: the auxv cell holds the
   auxv base [av], the first auxv pair is (33, vb), the vDSO image is mapped at [vb] in the
   run's segment list ([rvdso_rom]), and the 0x70-byte frame fits the stack above [lo]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Decode VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RVdsoAddr RVdsoSegs RVdsoSym.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma land_ones64_l : forall w : word, Z.land 18446744073709551615 (bv_unsigned w) = bv_unsigned w.
Proof.
  intros w. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. exact R.
Qed.

Lemma land_ones64_r : forall w : word, Z.land (bv_unsigned w) 18446744073709551615 = bv_unsigned w.
Proof. intros w. rewrite Z.land_comm. apply land_ones64_l. Qed.

(* ------------------------------------------------------------------ *)
(* The walk's tactics.                                                 *)
(* ------------------------------------------------------------------ *)

(* A closed integer expression: numerals and arithmetic over them.  Anything else -- a
   variable, a register, a read -- is refused, so nothing open is ever handed to
   [vm_compute].  It returns [tt] or fails: an Ltac function whose result a [let] binds
   must be a pure value, never a tactic sequence. *)
Local Ltac vclosedZ c :=
  lazymatch c with
  | Z0 => constr:(tt)
  | Zpos _ => constr:(tt)
  | Zneg _ => constr:(tt)
  | Z.add ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.sub ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.mul ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.opp ?a => vclosedZ a
  | Z.shiftl ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.shiftr ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.land ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.lor ?a ?b => let k := vclosedZ a in vclosedZ b
  | Z.lxor ?a ?b => let k := vclosedZ a in vclosedZ b
  | bv_unsigned (Z_to_bv _ ?a) => vclosedZ a
  | bv_signed (Z_to_bv _ ?a) => vclosedZ a
  | bv_wrap _ ?a => vclosedZ a
  | bv_unsigned (@BV _ ?a _) => vclosedZ a
  | _ => fail 1 "vclosedZ: not a closed Z expression"
  end.

(* The image offset an address names: the address with [vb] set to 0, which must be
   closed.  Its correctness is not assumed: [vaddr_eq] proves the address equal to
   [vb + o] before the read is used. *)
Local Ltac vdso_off vb E :=
  lazymatch E with
  | context [vb] =>
      let f := eval pattern vb in E in
      lazymatch f with
      | ?g vb =>
          let t := eval cbv beta in (g 0) in
          let k := vclosedZ t in
          let o := eval vm_compute in t in
          zlit o
      end
  | _ => fail 1 "vdso_off: address does not mention the vDSO base"
  end.

(* Unwrap [bv_unsigned (Z_to_bv 64 z)] wherever lia bounds [z], and fold closed arithmetic. *)
Local Ltac vzred :=
  fold_closed_in_goal;
  repeat (match goal with
          | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
          end; fold_closed_in_goal).

Local Ltac vaddr_eq :=
  unfold wa; first [ reflexivity | f_equal; vzred; lia ].

(* A read of [n] bytes of the vDSO image.  The bytes are the image's own, computed as a
   literal list from [rvdso_bytes]; [rvdso_ok] comes from the memory-free [rvdso_rom] and
   the goal's own [mem_inv]. *)
Local Ltac solve_load_vdso :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    lazymatch goal with
    | ROM : rvdso_rom segs ?vb, MI : mem_inv segs m |- _ =>
        let E := addr_expr a in
        let o := vdso_off vb E in
        let bs := eval vm_compute in (firstn n (skipn (Z.to_nat o) rvdso_bytes)) in
        let RD := fresh "RDV" in
        assert (RD : ov_read_bytes segs m (wa (vb + o)) n = Some bs)
          by (apply (rvdso_read segs m vb o n bs (rvdso_ok_of_rom segs m vb ROM MI));
              [ lia | rewrite RVDSO_SIZE_val; lia | vm_compute; reflexivity ]);
        replace (ov_read_bytes segs m a n) with (Some bs)
          by (rewrite <- RD; f_equal; vaddr_eq);
        clear RD; load_post
    end
  end.

Local Ltac solve_load ::= first [ solve_load_base | solve_load_image | solve_load_vdso ].

(* A branch is taken only where its condition is PROVED true or false. *)
Local Ltac vcond := unfold_cond; fold_lit_ux; vzred; solve_cond_rec.
Local Ltac vif :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by (symmetry; vcond); cbv iota
            | replace c with false by (symmetry; vcond); cbv iota ]
  end.

(* A comparison result held in a register ([seqz], [sltu]) whose operands are open: decide
   the comparison by proof, then fold. *)
Local Ltac vbool_once :=
  first
  [ match goal with |- context [v_sltiu _ _] => unfold v_sltiu end
  | match goal with |- context [v_sltu _ _] => unfold v_sltu, c_ltu end
  | match goal with
    | |- context [Z.ltb ?a ?b] =>
        first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; vzred; lia)
              | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; vzred; lia) ]
    end
  | match goal with
    | |- context [Z.eqb ?a ?b] =>
        first [ replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; vzred; lia)
              | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; vzred; lia) ]
    end
  | progress (cbv beta iota)
  | progress fold_closed_in_goal
  | progress (rewrite ?land_ones64_l, ?land_ones64_r)
  | progress (rewrite ?Z_to_bv_lit_self) ].
Local Ltac vbool := progress (repeat vbool_once).

Local Ltac vone := first [ step | vif | vbool ].

Section Walk.
  Variable tail : list Segment.

  Local Notation VS := (rvsegs tail).

  (* [a0] and [a1] are the two strings cgt_init passes: "LINUX_4.15" and
     "__vdso_clock_gettime" in the binary's read-only data ([RVdsoAddr.v]). *)
  Lemma vdsosym_walk :
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
           (a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo av vb : Z),
      ro_cells VS m VW_AUXV_CELL [C8 (Z_to_bv 64 av)] ->
      ro_cells VS m av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 vb)] ->
      rvdso_rom VS vb -> 0 < vb ->
      mem_inv VS m -> stk VS m lo (bv_unsigned sp) ->
      VW_AUXV_CELL + 8 <= lo -> lo + 112 <= bv_unsigned sp -> bv_unsigned sp <= av ->
      evt VS
        (vdsosym_post_v tail vb ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 VW_VERNAME) (Z_to_bv 64 VW_NAME)
                 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_vdsosym) fc None m (seg_rom VS)).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m lo av vb
           CELL AUX ROM VBP MI ST CLO LOB SPA.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof ROM as (VB0 & VBA & VBH & _). rewrite RVDSO_SPAN_val in VBH.
    unfold VW_AUXV_CELL in CELL, CLO.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl VS m) as WM.
    unfold P_vdsosym, VW_ENTRY, VW_VERNAME, VW_NAME.
    (* addi sp, sp, -0x70, then the frame *)
    step. carve_frame 112%nat ST.
    repeat vone.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc ra) _ _ _ _) => idtac
    | _ => step
    end.
    release_frame FR ST (bv_unsigned sp).
    finish.
    all: unfold RVDSO_CGT_OFF; vaddr_eq.
  Qed.

End Walk.
