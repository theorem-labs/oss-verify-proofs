(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HBRefused HBFullDefs HBFull.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require BS6HoleKA0 BFeHoleA0 BFeHoleOA0 BFeHoleRA0 BS6HoleKA2 BFeHoleA2 BFeHoleOA2 BFeHoleRA2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require BS6HoleKA3 BFeHoleA3 BFeHoleOA3 BFeHoleRA3 BS6HoleKA1 BFeHoleA1 BFeHoleOA1 BFeHoleRA1.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require BS6HoleKB0 BFeHoleB0 BFeHoleOB0 BFeHoleRB0 BS6HoleKB2 BFeHoleB2 BFeHoleOB2 BFeHoleRB2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require BS6HoleKB3 BFeHoleB3 BFeHoleOB3 BFeHoleRB3 BS6HoleKB1 BFeHoleB1 BFeHoleOB1 BFeHoleRB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem refused_leaf_closed : HBFullDefs.file_leaf_stmt HBFullDefs.REFUSED HBFullDefs.T_refused.
Proof.
  intros lim Hlim sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hva Hve Hfit Huid Hargc cont Hne Hsl Hdr Hln Hlk HC.
  unfold HBFullDefs.REFUSED in HC. change (2 ^ 26) with 67108864 in HC.
  exact (HBRefused.refused_leaf sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hargc cont Hne Hsl Hdr Hln Hlk
           (BS6HoleKA0.s6_hole_ka0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA0.fe_hole_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOA0.fe_hole_oa0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleRA0.fe_hole_ra0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (BS6HoleKA2.s6_hole_ka2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA2.fe_hole_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOA2.fe_hole_oa2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleRA2.fe_hole_ra2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (BS6HoleKA3.s6_hole_ka3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA3.fe_hole_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOA3.fe_hole_oa3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleRA3.fe_hole_ra3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (BS6HoleKA1.s6_hole_ka1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA1.fe_hole_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOA1.fe_hole_oa1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleRA1.fe_hole_ra1 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (BS6HoleKB0.s6_hole_kb0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB0.fe_hole_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOB0.fe_hole_ob0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleRB0.fe_hole_rb0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (BS6HoleKB2.s6_hole_kb2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB2.fe_hole_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOB2.fe_hole_ob2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleRB2.fe_hole_rb2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (BS6HoleKB3.s6_hole_kb3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB3.fe_hole_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOB3.fe_hole_ob3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleRB3.fe_hole_rb3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (BS6HoleKB1.s6_hole_kb1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB1.fe_hole_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOB1.fe_hole_ob1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleRB1.fe_hole_rb1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) HC).
Qed.

Definition ha_full_r (L0 : HBFullDefs.file_leaf_stmt HBFullDefs.K0 HBFullDefs.T_file) (LK : HBFullDefs.file_leaf_stmt HBFullDefs.KGE1 HBFullDefs.T_file) :=
  HBFull.ha_full L0 LK refused_leaf_closed.

Check ha_full_r.
