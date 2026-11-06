(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module F_fmt_fp.

Import Stdlib.ZArith.ZArith.
Open Scope Z_scope.

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

Definition FMT_FP_DEPTH : Z := 4640.

Definition fmt_fp_facts (y fl p t : Z) : Prop := False.

End G.
End F_fmt_fp.

Inductive shp := S8 | S4 | SB4.
