(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HBConeW.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require BS6HoleA0 BFeHoleA0 BFeHoleOA0 BFeHoleDA0 BFeHoleHA0 BS6HoleA2 BFeHoleA2 BFeHoleOA2 BFeHoleDA2 BFeHoleHA2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require BS6HoleA3 BFeHoleA3 BFeHoleOA3 BFeHoleDA3 BFeHoleHA3 BS6HoleA1 BFeHoleA1 BFeHoleOA1 BFeHoleDA1 BFeHoleHA1.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require BS6HoleB0 BFeHoleB0 BFeHoleOB0 BFeHoleDB0 BFeHoleHB0 BS6HoleB2 BFeHoleB2 BFeHoleOB2 BFeHoleDB2 BFeHoleHB2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HBX Require BS6HoleB3 BFeHoleB3 BFeHoleOB3 BFeHoleDB3 BFeHoleHB3 BS6HoleB1 BFeHoleB1 BFeHoleOB1 BFeHoleDB1 BFeHoleHB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition haw_cone_closed sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid :=
  HBConeW.ha_cone sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid
    (BS6HoleA0.s6_hole_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA0.fe_hole_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOA0.fe_hole_oa0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleDA0.fe_hole_da0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleHA0.fe_hole_ha0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (BS6HoleA2.s6_hole_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA2.fe_hole_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOA2.fe_hole_oa2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleDA2.fe_hole_da2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleHA2.fe_hole_ha2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (BS6HoleA3.s6_hole_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA3.fe_hole_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOA3.fe_hole_oa3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleDA3.fe_hole_da3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleHA3.fe_hole_ha3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (BS6HoleA1.s6_hole_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleA1.fe_hole_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOA1.fe_hole_oa1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleDA1.fe_hole_da1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleHA1.fe_hole_ha1 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (BS6HoleB0.s6_hole_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB0.fe_hole_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOB0.fe_hole_ob0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleDB0.fe_hole_db0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleHB0.fe_hole_hb0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (BS6HoleB2.s6_hole_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB2.fe_hole_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOB2.fe_hole_ob2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleDB2.fe_hole_db2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleHB2.fe_hole_hb2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (BS6HoleB3.s6_hole_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB3.fe_hole_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOB3.fe_hole_ob3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleDB3.fe_hole_db3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleHB3.fe_hole_hb3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
    (BS6HoleB1.s6_hole_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleB1.fe_hole_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleOB1.fe_hole_ob1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleDB1.fe_hole_db1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (BFeHoleHB1.fe_hole_hb1 sp rdraw brk0 argv envp fs uid hw Hsp Hva).

Check haw_cone_closed.
