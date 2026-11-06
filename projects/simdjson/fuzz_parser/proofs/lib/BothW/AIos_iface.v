(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation mem := (word -> option byte).
Definition ios_char_shared (m : mem) : Prop := True.
Definition ios_cout (m : mem) : Prop := True.
Definition ios_clog (m : mem) : Prop := True.
Definition ios_wide_shared (m : mem) : Prop := True.
Definition ios_wcout (m : mem) : Prop := True.
Definition ios_wclog (m : mem) : Prop := True.
Definition ios_cells (m : mem) : Prop := True.
Lemma ios_cells_any : forall m, ios_cells m.
Proof. intros; exact I. Qed.
