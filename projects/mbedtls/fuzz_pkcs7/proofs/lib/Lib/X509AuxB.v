(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep X509Aux.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac goal_vars_in T :=
  lazymatch goal with |- ?G =>
    assert_fails (idtac; match G with context [?v] => is_var v;
                    lazymatch type of v with Z => idtac | bv _ => idtac end;
                    lazymatch T with context [v] => fail | _ => idtac end end)
  end.

Ltac lia_alldisj :=
  match goal with H : ?A \/ ?B |- _ =>
    goal_vars_in (A \/ B); let H1 := fresh "HD" in destruct H as [H1|H1]; clear_disj; lia end.

(* [comment removed for export] *)
Ltac lia_one_disj_rel :=
  match goal with H : ?A \/ ?B |- _ =>
    mentions_goal_var (A \/ B); let H1 := fresh "HD" in destruct H as [H1|H1]; clear_disj; lia end.

(* [comment removed for export] *)
Ltac lia_sep ::= first [ lia_nodisj | lia_alldisj | lia_one_disj_rel ].

(* [comment removed for export] *)
Ltac slia_cheap :=
  first [ exact I
        | lazymatch goal with |- _ /\ _ => split; [ first [ lia_nodisj | lia_alldisj ] | slia_cheap ] end
        | first [ lia_nodisj | lia_alldisj ] ].


(* [comment removed for export] *)
Ltac flia2 := first [ lia_nodisj | lia_alldisj ].

(* [comment removed for export] *)
Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  (* [comment removed for export] *)
  repeat match goal with
  | H : rw_cells segs m ?A2 _ |- _ => lazymatch W with context [(A2, _)] => clear H end
  | H : bytes_at segs m ?A2 _ |- _ => lazymatch W with context [(A2, _)] => clear H end
  end;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      (* [comment removed for export] *)
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia_cheap ]
            | clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_munch segs L W m m') in H; [ | exact MU | cbn [outside]; intros; slia ]
            | idtac "note: dropping statics_ok (callee footprint not provably outside the data range):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_munch lo hi E W m m') in H; [ | exact MU | cbn [outside]; intros; slia ]
            | idtac "note: dropping pristine (callee footprint not provably outside its range):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.


(* [comment removed for export] *)
Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia_nodisj | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia_nodisj | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.
