(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Cells Step.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool04list04true37Corelib4Init5Logicia2eq37Corelib7Numbers7BinNumsk34Nposk31Z89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Image8WithSegs~~~~~~m7aro_bytes_b79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~r98ro_bytes35stdpp9bitvectorbdefinitionsve2bv06length79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hi84cell46Stdlib6ZArith6BinInt1Zhmc2le04cons03nil06optionhi82CBr97mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hqd8ro_cellshmc3addhmc6of_nathmc3pow3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeigc7Segment" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : ltac2:(zQ "20!he!ik1@1$0$1").

Fixpoint ro_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A) with
      | Some b' => bv_eqb b b' && ro_addr segs (wa A) && ro_bytes_b (A + 1) bs'
      | None => false
      end
  end.

Lemma ro_bytes_b_sound : ltac2:(zQ "90!h8!he!i4!je!lc!m3!qc!v3!hhb>2bs@1$1@1$8@1$4#8>1A$5>0@3$3$0@2$6^1^2$2@3$7?4segs^2^3").
Proof.
  induction bs as [|b bs IH]; intros A H; cbn in *; [exact I|].
  destruct (seg_rom segs (wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H3]. apply andb_prop in H1. destruct H1 as [H1 H2].
  unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  split; [split; [exact E| exact H2]|]. apply IH. exact H3.
Qed.

Lemma ro_cells_image : ltac2:(zQ "h40!lc!hhb!hi0!hm4!ho4!h8!hoa!he!hp0!hp5!i4!je!m3!hpd!qc!hq3!hu8!hv4!hvb!ig5>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$c>2bs@1$7@1$1@1$0#8>0@2$f?4segs^3>0@3$b$5@2$e^3^2$a>0@2$4Z^4>0@2$4@2$h1^5@1$h2@2$2@1$1@1$0#8^4@2$h3+2+k0@4$h0?4segs^7^6@3$6$3@2$d@2$2@1$1@1$0#8^5^5@1$8$3").
Proof.
  intros m A bs Hinv Hb HA Hl. split.
  - cbn. split; [reflexivity|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; try assumption.
    apply ro_bytes_b_sound. exact Hb.
Qed.

(* [comment removed for export] *)
Fixpoint image_bytes (A : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match seg_rom segs (wa A), image_bytes (A + 1) n' with
            | Some b, Some bs => Some (b :: bs)
            | _, _ => None
            end
  end.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
