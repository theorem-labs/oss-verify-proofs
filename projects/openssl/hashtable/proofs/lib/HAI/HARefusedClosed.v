(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.openssl.hashtable.lib Require HARefused HAFullDefs HAFull.
From OSSVerify.Proofs.openssl.hashtable.lib.HAX Require S6HoleKA0 FeHoleA0 FeHoleOA0 FeHoleRA0 S6HoleKA2 FeHoleA2 FeHoleOA2 FeHoleRA2.
From OSSVerify.Proofs.openssl.hashtable.lib.HAX Require S6HoleKA3 FeHoleA3 FeHoleOA3 FeHoleRA3 S6HoleKA1 FeHoleA1 FeHoleOA1 FeHoleRA1.
From OSSVerify.Proofs.openssl.hashtable.lib.HAX Require S6HoleKB0 FeHoleB0 FeHoleOB0 FeHoleRB0 S6HoleKB2 FeHoleB2 FeHoleOB2 FeHoleRB2.
From OSSVerify.Proofs.openssl.hashtable.lib.HAX Require S6HoleKB3 FeHoleB3 FeHoleOB3 FeHoleRB3 S6HoleKB1 FeHoleB1 FeHoleOB1 FeHoleRB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem refused_leaf_closed : HAFullDefs.file_leaf_stmt HAFullDefs.REFUSED HAFullDefs.T_refused.
Proof.
  intros lim Hlim sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hva Hve Hfit Huid Hargc cont Hne Hsl Hdr Hln Hlk HC.
  unfold HAFullDefs.REFUSED in HC. change (2 ^ 26) with 67108864 in HC.
  exact (HARefused.refused_leaf sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hargc cont Hne Hsl Hdr Hln Hlk
           (S6HoleKA0.s6_hole_ka0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA0.fe_hole_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA0.fe_hole_oa0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleRA0.fe_hole_ra0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (S6HoleKA2.s6_hole_ka2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA2.fe_hole_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA2.fe_hole_oa2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleRA2.fe_hole_ra2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (S6HoleKA3.s6_hole_ka3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA3.fe_hole_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA3.fe_hole_oa3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleRA3.fe_hole_ra3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (S6HoleKA1.s6_hole_ka1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA1.fe_hole_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA1.fe_hole_oa1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleRA1.fe_hole_ra1 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (S6HoleKB0.s6_hole_kb0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB0.fe_hole_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB0.fe_hole_ob0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleRB0.fe_hole_rb0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (S6HoleKB2.s6_hole_kb2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB2.fe_hole_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB2.fe_hole_ob2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleRB2.fe_hole_rb2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (S6HoleKB3.s6_hole_kb3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB3.fe_hole_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB3.fe_hole_ob3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleRB3.fe_hole_rb3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
           (S6HoleKB1.s6_hole_kb1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB1.fe_hole_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB1.fe_hole_ob1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleRB1.fe_hole_rb1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) HC).
Qed.

Definition ha_full_r (L0 : HAFullDefs.file_leaf_stmt HAFullDefs.K0 HAFullDefs.T_file) (LK : HAFullDefs.file_leaf_stmt HAFullDefs.KGE1 HAFullDefs.T_file) :=
  HAFull.ha_full L0 LK refused_leaf_closed.

Check ha_full_r.
