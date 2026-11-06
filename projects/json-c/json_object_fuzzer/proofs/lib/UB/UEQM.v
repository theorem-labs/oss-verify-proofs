(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)


From OSSVerify.json_c.json_object_fuzzer.images Require Export Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition rsegs := Ubsan.M.loaded_segments.
