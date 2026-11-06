(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record rfj := mkJ {
j_flags : word; j_pad0 : list byte; j_close : word; j_wend : word; j_wpos : word; j_mbz1 : word; j_wbase : word;
j_read : word; j_write : word; j_seek : word; j_bufsize : word; j_prev : word; j_next : word;
j_fd : word; j_ppid : word; j_lockcount : word; j_mode : word; j_lock : word; j_lbf : word; j_pad1 : list byte;
j_cookie : word; j_off : word; j_getln : word; j_mbz2 : word; j_pl : word; j_nl : word; j_locale : word }.
