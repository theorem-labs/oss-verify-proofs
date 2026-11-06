(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require HAConeW.
From OSSVerify.Proofs.openssl.hashtable.lib.HAX Require S6HoleA0 FeHoleA0 FeHoleOA0 FeHoleDA0 FeHoleHA0 S6HoleA2 FeHoleA2 FeHoleOA2 FeHoleDA2 FeHoleHA2.
From OSSVerify.Proofs.openssl.hashtable.lib.HAX Require S6HoleA3 FeHoleA3 FeHoleOA3 FeHoleDA3 FeHoleHA3 S6HoleA1 FeHoleA1 FeHoleOA1 FeHoleDA1 FeHoleHA1.
From OSSVerify.Proofs.openssl.hashtable.lib.HAX Require S6HoleB0 FeHoleB0 FeHoleOB0 FeHoleDB0 FeHoleHB0 S6HoleB2 FeHoleB2 FeHoleOB2 FeHoleDB2 FeHoleHB2.
From OSSVerify.Proofs.openssl.hashtable.lib.HAX Require S6HoleB3 FeHoleB3 FeHoleOB3 FeHoleDB3 FeHoleHB3 S6HoleB1 FeHoleB1 FeHoleOB1 FeHoleDB1 FeHoleHB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition haw_cone_closed sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid :=
  HAConeW.ha_cone sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid
    (S6HoleA0.s6_hole_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA0.fe_hole_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA0.fe_hole_oa0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleDA0.fe_hole_da0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleHA0.fe_hole_ha0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (S6HoleA2.s6_hole_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA2.fe_hole_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA2.fe_hole_oa2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleDA2.fe_hole_da2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleHA2.fe_hole_ha2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (S6HoleA3.s6_hole_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA3.fe_hole_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA3.fe_hole_oa3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleDA3.fe_hole_da3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleHA3.fe_hole_ha3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (S6HoleA1.s6_hole_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA1.fe_hole_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA1.fe_hole_oa1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleDA1.fe_hole_da1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleHA1.fe_hole_ha1 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (S6HoleB0.s6_hole_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB0.fe_hole_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB0.fe_hole_ob0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleDB0.fe_hole_db0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleHB0.fe_hole_hb0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (S6HoleB2.s6_hole_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB2.fe_hole_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB2.fe_hole_ob2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleDB2.fe_hole_db2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleHB2.fe_hole_hb2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (S6HoleB3.s6_hole_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB3.fe_hole_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB3.fe_hole_ob3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleDB3.fe_hole_db3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleHB3.fe_hole_hb3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (S6HoleB1.s6_hole_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB1.fe_hole_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB1.fe_hole_ob1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleDB1.fe_hole_db1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleHB1.fe_hole_hb1 sp rdraw brk0 argv envp fs uid hw Hsp Hva).

Check haw_cone_closed.
