(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up plan's fresh-variable indices and the CONFIG_RSEQ flag of its snapshots). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import StartupJSAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition startup_plan_wsplit1 : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PMprotect  (* [comment removed for export] *)
   (
    PSpin  (* [comment removed for export] *))
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PX XIMemset []  (* [comment removed for export] *)
         (
          PRun []  (* [comment removed for export] *)
          (
           PX XIMemset []  (* [comment removed for export] *)
           (
            PBump 184  (* [comment removed for export] *)
            (
             PFog 1 8192  (* [comment removed for export] *)
             (
              PShDisj (escale 4096 (EVar 61)) (ELit 0xb09000) (eaddz (escale 4096 (EVar 86)) 4096) (ELit 4096)  (* [comment removed for export] *)
              (
               PUnvis (eaddz (escale 4096 (EVar 86)) 4096) (ELit 4096)  (* [comment removed for export] *)
               (
                PGhost (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                (
                 PHavocBrk 0x61e000 0x80620000  (* [comment removed for export] *)
                 (
                  PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat  (* [comment removed for export] *)
                  (
                   PMerge 0  (* [comment removed for export] *)))))))))))))))))).

Definition startup_plan_viafail2 : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PBump 86  (* [comment removed for export] *)
   (
    PMmap  (* [comment removed for export] *)
    (
     PSpin  (* [comment removed for export] *))
    (
     PShDisj (escale 4096 (EVar 86)) (ELit 0x2000) e_band e_bandlen  (* [comment removed for export] *)
     (
      PShDisj (escale 4096 (EVar 86)) (ELit 0x2000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 86))  (* [comment removed for export] *)
       (
        startup_plan_wsplit1)
       (
        startup_plan_wsplit1)))))).

Definition startup_plan_tail3 : plan :=
  PRun [0x3ffbc]  (* [comment removed for export] *)
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
           (
            PRun []  (* [comment removed for export] *)
            (
             PX XIMemcpy []  (* [comment removed for export] *)
             (
              PRun []  (* [comment removed for export] *)
              (
               PMmap  (* [comment removed for export] *)
               (
                PSpin  (* [comment removed for export] *))
               (
                PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                (
                 PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                 (
                  PRun []  (* [comment removed for export] *)
                  (
                   PX XIMemcpy []  (* [comment removed for export] *)
                   (
                    PRun []  (* [comment removed for export] *)
                    (
                     PX XIMemcpy []  (* [comment removed for export] *)
                     (
                      PRun []  (* [comment removed for export] *)
                      (
                       PX XMemset []  (* [comment removed for export] *)
                       (
                        PRun []  (* [comment removed for export] *)
                        (
                         PX XMemset []  (* [comment removed for export] *)
                         (
                          PRun []  (* [comment removed for export] *)
                          (
                           PX XMemset []  (* [comment removed for export] *)
                           (
                            PRun []  (* [comment removed for export] *)
                            (
                             PX XMemset []  (* [comment removed for export] *)
                             (
                              PRun []  (* [comment removed for export] *)
                              (
                               PX XMemset []  (* [comment removed for export] *)
                               (
                                PRun []  (* [comment removed for export] *)
                                (
                                 PX XMemset []  (* [comment removed for export] *)
                                 (
                                  PRun []  (* [comment removed for export] *)
                                  (
                                   PX XMemset []  (* [comment removed for export] *)
                                   (
                                    PRun []  (* [comment removed for export] *)
                                    (
                                     PX XMemset []  (* [comment removed for export] *)
                                     (
                                      PRun []  (* [comment removed for export] *)
                                      (
                                       PX XMemset []  (* [comment removed for export] *)
                                       (
                                        PRun []  (* [comment removed for export] *)
                                        (
                                         PX XMemset []  (* [comment removed for export] *)
                                         (
                                          PRun []  (* [comment removed for export] *)
                                          (
                                           PX XMemset []  (* [comment removed for export] *)
                                           (
                                            PRun []  (* [comment removed for export] *)
                                            (
                                             PX XMemset []  (* [comment removed for export] *)
                                             (
                                              PRun []  (* [comment removed for export] *)
                                              (
                                               PX XMemset []  (* [comment removed for export] *)
                                               (
                                                PRun []  (* [comment removed for export] *)
                                                (
                                                 PX XMemset []  (* [comment removed for export] *)
                                                 (
                                                  PRun []  (* [comment removed for export] *)
                                                  (
                                                   PX XMemset []  (* [comment removed for export] *)
                                                   (
                                                    PRun []  (* [comment removed for export] *)
                                                    (
                                                     PX XMemset []  (* [comment removed for export] *)
                                                     (
                                                      PRun []  (* [comment removed for export] *)
                                                      (
                                                       PX XMemset []  (* [comment removed for export] *)
                                                       (
                                                        PRun []  (* [comment removed for export] *)
                                                        (
                                                         PX XMemset []  (* [comment removed for export] *)
                                                         (
                                                          PRun []  (* [comment removed for export] *)
                                                          (
                                                           PX XMemset []  (* [comment removed for export] *)
                                                           (
                                                            PRun []  (* [comment removed for export] *)
                                                            (
                                                             PX XMemset []  (* [comment removed for export] *)
                                                             (
                                                              PRun []  (* [comment removed for export] *)
                                                              (
                                                               PX XMemset []  (* [comment removed for export] *)
                                                               (
                                                                PRun []  (* [comment removed for export] *)
                                                                (
                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                 (
                                                                  PRun []  (* [comment removed for export] *)
                                                                  (
                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                   (
                                                                    PRun []  (* [comment removed for export] *)
                                                                    (
                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                     (
                                                                      PRun []  (* [comment removed for export] *)
                                                                      (
                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                       (
                                                                        PRun []  (* [comment removed for export] *)
                                                                        (
                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                         (
                                                                          PRun []  (* [comment removed for export] *)
                                                                          (
                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                           (
                                                                            PRun []  (* [comment removed for export] *)
                                                                            (
                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                             (
                                                                              PRun []  (* [comment removed for export] *)
                                                                              (
                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                               (
                                                                                PRun []  (* [comment removed for export] *)
                                                                                (
                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                 (
                                                                                  PRun []  (* [comment removed for export] *)
                                                                                  (
                                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun []  (* [comment removed for export] *)
                                                                                    (
                                                                                     PMmap  (* [comment removed for export] *)
                                                                                     (
                                                                                      PSpin  (* [comment removed for export] *))
                                                                                     (
                                                                                      PShDisj (escale 4096 (EVar 591)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                      (
                                                                                       PShDisj (escale 4096 (EVar 591)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun []  (* [comment removed for export] *)
                                                                                        (
                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun []  (* [comment removed for export] *)
                                                                                          (
                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun []  (* [comment removed for export] *)
                                                                                            (
                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                             (
                                                                                              PRun [0x81418]  (* [comment removed for export] *)
                                                                                              (
                                                                                               PHandoff 0  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail4 : plan :=
  PRun [0x3ffbc]  (* [comment removed for export] *)
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
           (
            PRun []  (* [comment removed for export] *)
            (
             PX XIMemcpy []  (* [comment removed for export] *)
             (
              PRun []  (* [comment removed for export] *)
              (
               PMmap  (* [comment removed for export] *)
               (
                PSpin  (* [comment removed for export] *))
               (
                PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                (
                 PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                 (
                  PRun []  (* [comment removed for export] *)
                  (
                   PX XIMemcpy []  (* [comment removed for export] *)
                   (
                    PRun []  (* [comment removed for export] *)
                    (
                     PX XIMemcpy []  (* [comment removed for export] *)
                     (
                      PRun []  (* [comment removed for export] *)
                      (
                       PX XMemset []  (* [comment removed for export] *)
                       (
                        PRun []  (* [comment removed for export] *)
                        (
                         PX XMemset []  (* [comment removed for export] *)
                         (
                          PRun []  (* [comment removed for export] *)
                          (
                           PX XMemset []  (* [comment removed for export] *)
                           (
                            PRun []  (* [comment removed for export] *)
                            (
                             PX XMemset []  (* [comment removed for export] *)
                             (
                              PRun []  (* [comment removed for export] *)
                              (
                               PX XMemset []  (* [comment removed for export] *)
                               (
                                PRun []  (* [comment removed for export] *)
                                (
                                 PX XMemset []  (* [comment removed for export] *)
                                 (
                                  PRun []  (* [comment removed for export] *)
                                  (
                                   PX XMemset []  (* [comment removed for export] *)
                                   (
                                    PRun []  (* [comment removed for export] *)
                                    (
                                     PX XMemset []  (* [comment removed for export] *)
                                     (
                                      PRun []  (* [comment removed for export] *)
                                      (
                                       PX XMemset []  (* [comment removed for export] *)
                                       (
                                        PRun []  (* [comment removed for export] *)
                                        (
                                         PX XMemset []  (* [comment removed for export] *)
                                         (
                                          PRun []  (* [comment removed for export] *)
                                          (
                                           PX XMemset []  (* [comment removed for export] *)
                                           (
                                            PRun []  (* [comment removed for export] *)
                                            (
                                             PX XMemset []  (* [comment removed for export] *)
                                             (
                                              PRun []  (* [comment removed for export] *)
                                              (
                                               PX XMemset []  (* [comment removed for export] *)
                                               (
                                                PRun []  (* [comment removed for export] *)
                                                (
                                                 PX XMemset []  (* [comment removed for export] *)
                                                 (
                                                  PRun []  (* [comment removed for export] *)
                                                  (
                                                   PX XMemset []  (* [comment removed for export] *)
                                                   (
                                                    PRun []  (* [comment removed for export] *)
                                                    (
                                                     PX XMemset []  (* [comment removed for export] *)
                                                     (
                                                      PRun []  (* [comment removed for export] *)
                                                      (
                                                       PX XMemset []  (* [comment removed for export] *)
                                                       (
                                                        PRun []  (* [comment removed for export] *)
                                                        (
                                                         PX XMemset []  (* [comment removed for export] *)
                                                         (
                                                          PRun []  (* [comment removed for export] *)
                                                          (
                                                           PX XMemset []  (* [comment removed for export] *)
                                                           (
                                                            PRun []  (* [comment removed for export] *)
                                                            (
                                                             PX XMemset []  (* [comment removed for export] *)
                                                             (
                                                              PRun []  (* [comment removed for export] *)
                                                              (
                                                               PX XMemset []  (* [comment removed for export] *)
                                                               (
                                                                PRun []  (* [comment removed for export] *)
                                                                (
                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                 (
                                                                  PRun []  (* [comment removed for export] *)
                                                                  (
                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                   (
                                                                    PRun []  (* [comment removed for export] *)
                                                                    (
                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                     (
                                                                      PRun []  (* [comment removed for export] *)
                                                                      (
                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                       (
                                                                        PRun []  (* [comment removed for export] *)
                                                                        (
                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                         (
                                                                          PRun []  (* [comment removed for export] *)
                                                                          (
                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                           (
                                                                            PRun []  (* [comment removed for export] *)
                                                                            (
                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                             (
                                                                              PRun []  (* [comment removed for export] *)
                                                                              (
                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                               (
                                                                                PRun []  (* [comment removed for export] *)
                                                                                (
                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                 (
                                                                                  PRun []  (* [comment removed for export] *)
                                                                                  (
                                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun []  (* [comment removed for export] *)
                                                                                    (
                                                                                     PMmap  (* [comment removed for export] *)
                                                                                     (
                                                                                      PSpin  (* [comment removed for export] *))
                                                                                     (
                                                                                      PShDisj (escale 4096 (EVar 591)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                      (
                                                                                       PShDisj (escale 4096 (EVar 591)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun []  (* [comment removed for export] *)
                                                                                        (
                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun []  (* [comment removed for export] *)
                                                                                          (
                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun []  (* [comment removed for export] *)
                                                                                            (
                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                             (
                                                                                              PRun [0x81418]  (* [comment removed for export] *)
                                                                                              (
                                                                                               PHandoff 1000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* CW44: the recorded join snapshots [js_0] / [js_3] now take
   the run's CONFIG_RSEQ flag, because nine of their stack-geometry rows differ between
   the two arms by exactly one numeral (#38's auxv gains the two AT_RSEQ pairs, 32 bytes).
   The four definitions between here and [startup_plan] carry the flag for no other
   reason; no node's text changes.  See StartupJSAsan.v's header for the measurement. *)
Definition startup_plan_via_U (r : Z) : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PRename [(47, 12); (48, 13); (81, 14); (210, 15); (227, 16); (228, 17); (20, 18); (246, 19); (247, 20); (21, 21); (361, 22); (362, 23); (395, 28); (428, 61); (430, 29); (431, 30); (432, 31); (436, 32); (437, 33); (438, 34); (439, 35); (441, 36); (442, 37); (443, 38); (444, 39)]%nat  (* [comment removed for export] *)
   (
   PVia 0 (js_0 r) 185  (* [comment removed for export] *)
   (
    PBrk2S  (* [comment removed for export] *)
    (
     startup_plan_viafail2)
    (
     PRun []  (* [comment removed for export] *)
     (
      PMmapIn  (* [comment removed for export] *)
      (
       PSpin  (* [comment removed for export] *))
      (
       PRun []  (* [comment removed for export] *)
       (
        PBump 86  (* [comment removed for export] *)
        (
         PIntroW 4295491576 [KRange (EVar 86) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 86)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6348800) (SA (escale 4096 (EVar 86)) 0) (ELit 8192)]  (* [comment removed for export] *)
         (
          PGhost (eaddz (escale 4096 (EVar 86)) 4096) (ELit 4096)  (* [comment removed for export] *)
          (
           PMmap  (* [comment removed for export] *)
           (
            PSpin  (* [comment removed for export] *))
           (
            PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
            (
             PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
             (
              PRun []  (* [comment removed for export] *)
              (
               PX XIMemset []  (* [comment removed for export] *)
               (
                PRun []  (* [comment removed for export] *)
                (
                 PX XIMemset []  (* [comment removed for export] *)
                 (
                  PBump 184  (* [comment removed for export] *)
                  (
                   PFog 1 8192  (* [comment removed for export] *)
                   (
                    PShDisj (escale 4096 (EVar 61)) (ELit 0xb09000) (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                    (
                     PUnvis (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                     (
                      PHavocBrk 0x61e000 0x80620000  (* [comment removed for export] *)
                      (
                       PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat  (* [comment removed for export] *)
                       (
                        PMerge 0  (* [comment removed for export] *)))))))))))))))))))
      (
       PSpin  (* [comment removed for export] *)))))
   (
    PRename [(28, 24); (61, 25); (86, 26); (87, 27); (184, 28); (185, 29); (186, 30); (187, 31); (188, 32); (189, 33); (190, 34); (191, 35); (192, 36); (193, 37); (194, 38); (195, 39); (196, 40); (197, 41); (198, 42); (199, 43)]%nat  (* [comment removed for export] *)
    (
     PCase2 (esub (eaddz (escale 16 (EVar 6)) 36703) (escale 4096 (EVar 24))) 4030  (* [comment removed for export] *)
     (
      startup_plan_tail3)
     (
       startup_plan_tail4))))).

Definition startup_plan_wsplit5 : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PMprotect  (* [comment removed for export] *)
   (
    PSpin  (* [comment removed for export] *))
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PX XIMemset []  (* [comment removed for export] *)
         (
          PRun []  (* [comment removed for export] *)
          (
           PX XIMemset []  (* [comment removed for export] *)
           (
            PBump 184  (* [comment removed for export] *)
            (
             PFog 1 8192  (* [comment removed for export] *)
             (
              PShDisj (escale 4096 (EVar 61)) (ELit 0xb09000) (eaddz (escale 4096 (EVar 86)) 4096) (ELit 4096)  (* [comment removed for export] *)
              (
               PUnvis (eaddz (escale 4096 (EVar 86)) 4096) (ELit 4096)  (* [comment removed for export] *)
               (
                PGhost (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                (
                 PHavocBrk 0x61e000 0x80620000  (* [comment removed for export] *)
                 (
                  PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat  (* [comment removed for export] *)
                  (
                   PMerge 3  (* [comment removed for export] *)))))))))))))))))).

Definition startup_plan_viafail6 : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PBump 86  (* [comment removed for export] *)
   (
    PMmap  (* [comment removed for export] *)
    (
     PSpin  (* [comment removed for export] *))
    (
     PShDisj (escale 4096 (EVar 86)) (ELit 0x2000) e_band e_bandlen  (* [comment removed for export] *)
     (
      PShDisj (escale 4096 (EVar 86)) (ELit 0x2000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 86))  (* [comment removed for export] *)
       (
        startup_plan_wsplit5)
       (
        startup_plan_wsplit5)))))).

Definition startup_plan_tail7 : plan :=
  PRun [0x3ffbc]  (* [comment removed for export] *)
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
           (
            PRun []  (* [comment removed for export] *)
            (
             PX XIMemcpy []  (* [comment removed for export] *)
             (
              PRun []  (* [comment removed for export] *)
              (
               PMmap  (* [comment removed for export] *)
               (
                PSpin  (* [comment removed for export] *))
               (
                PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                (
                 PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                 (
                  PRun []  (* [comment removed for export] *)
                  (
                   PX XIMemcpy []  (* [comment removed for export] *)
                   (
                    PRun []  (* [comment removed for export] *)
                    (
                     PX XIMemcpy []  (* [comment removed for export] *)
                     (
                      PRun []  (* [comment removed for export] *)
                      (
                       PX XMemset []  (* [comment removed for export] *)
                       (
                        PRun []  (* [comment removed for export] *)
                        (
                         PX XMemset []  (* [comment removed for export] *)
                         (
                          PRun []  (* [comment removed for export] *)
                          (
                           PX XMemset []  (* [comment removed for export] *)
                           (
                            PRun []  (* [comment removed for export] *)
                            (
                             PX XMemset []  (* [comment removed for export] *)
                             (
                              PRun []  (* [comment removed for export] *)
                              (
                               PX XMemset []  (* [comment removed for export] *)
                               (
                                PRun []  (* [comment removed for export] *)
                                (
                                 PX XMemset []  (* [comment removed for export] *)
                                 (
                                  PRun []  (* [comment removed for export] *)
                                  (
                                   PX XMemset []  (* [comment removed for export] *)
                                   (
                                    PRun []  (* [comment removed for export] *)
                                    (
                                     PX XMemset []  (* [comment removed for export] *)
                                     (
                                      PRun []  (* [comment removed for export] *)
                                      (
                                       PX XMemset []  (* [comment removed for export] *)
                                       (
                                        PRun []  (* [comment removed for export] *)
                                        (
                                         PX XMemset []  (* [comment removed for export] *)
                                         (
                                          PRun []  (* [comment removed for export] *)
                                          (
                                           PX XMemset []  (* [comment removed for export] *)
                                           (
                                            PRun []  (* [comment removed for export] *)
                                            (
                                             PX XMemset []  (* [comment removed for export] *)
                                             (
                                              PRun []  (* [comment removed for export] *)
                                              (
                                               PX XMemset []  (* [comment removed for export] *)
                                               (
                                                PRun []  (* [comment removed for export] *)
                                                (
                                                 PX XMemset []  (* [comment removed for export] *)
                                                 (
                                                  PRun []  (* [comment removed for export] *)
                                                  (
                                                   PX XMemset []  (* [comment removed for export] *)
                                                   (
                                                    PRun []  (* [comment removed for export] *)
                                                    (
                                                     PX XMemset []  (* [comment removed for export] *)
                                                     (
                                                      PRun []  (* [comment removed for export] *)
                                                      (
                                                       PX XMemset []  (* [comment removed for export] *)
                                                       (
                                                        PRun []  (* [comment removed for export] *)
                                                        (
                                                         PX XMemset []  (* [comment removed for export] *)
                                                         (
                                                          PRun []  (* [comment removed for export] *)
                                                          (
                                                           PX XMemset []  (* [comment removed for export] *)
                                                           (
                                                            PRun []  (* [comment removed for export] *)
                                                            (
                                                             PX XMemset []  (* [comment removed for export] *)
                                                             (
                                                              PRun []  (* [comment removed for export] *)
                                                              (
                                                               PX XMemset []  (* [comment removed for export] *)
                                                               (
                                                                PRun []  (* [comment removed for export] *)
                                                                (
                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                 (
                                                                  PRun []  (* [comment removed for export] *)
                                                                  (
                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                   (
                                                                    PRun []  (* [comment removed for export] *)
                                                                    (
                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                     (
                                                                      PRun []  (* [comment removed for export] *)
                                                                      (
                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                       (
                                                                        PRun []  (* [comment removed for export] *)
                                                                        (
                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                         (
                                                                          PRun []  (* [comment removed for export] *)
                                                                          (
                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                           (
                                                                            PRun []  (* [comment removed for export] *)
                                                                            (
                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                             (
                                                                              PRun []  (* [comment removed for export] *)
                                                                              (
                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                               (
                                                                                PRun []  (* [comment removed for export] *)
                                                                                (
                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                 (
                                                                                  PRun []  (* [comment removed for export] *)
                                                                                  (
                                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun []  (* [comment removed for export] *)
                                                                                    (
                                                                                     PMmap  (* [comment removed for export] *)
                                                                                     (
                                                                                      PSpin  (* [comment removed for export] *))
                                                                                     (
                                                                                      PShDisj (escale 4096 (EVar 591)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                      (
                                                                                       PShDisj (escale 4096 (EVar 591)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun []  (* [comment removed for export] *)
                                                                                        (
                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun []  (* [comment removed for export] *)
                                                                                          (
                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun []  (* [comment removed for export] *)
                                                                                            (
                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                             (
                                                                                              PRun [0x81418]  (* [comment removed for export] *)
                                                                                              (
                                                                                               PHandoff 2000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail8 : plan :=
  PRun [0x3ffbc]  (* [comment removed for export] *)
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
           (
            PRun []  (* [comment removed for export] *)
            (
             PX XIMemcpy []  (* [comment removed for export] *)
             (
              PRun []  (* [comment removed for export] *)
              (
               PMmap  (* [comment removed for export] *)
               (
                PSpin  (* [comment removed for export] *))
               (
                PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                (
                 PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                 (
                  PRun []  (* [comment removed for export] *)
                  (
                   PX XIMemcpy []  (* [comment removed for export] *)
                   (
                    PRun []  (* [comment removed for export] *)
                    (
                     PX XIMemcpy []  (* [comment removed for export] *)
                     (
                      PRun []  (* [comment removed for export] *)
                      (
                       PX XMemset []  (* [comment removed for export] *)
                       (
                        PRun []  (* [comment removed for export] *)
                        (
                         PX XMemset []  (* [comment removed for export] *)
                         (
                          PRun []  (* [comment removed for export] *)
                          (
                           PX XMemset []  (* [comment removed for export] *)
                           (
                            PRun []  (* [comment removed for export] *)
                            (
                             PX XMemset []  (* [comment removed for export] *)
                             (
                              PRun []  (* [comment removed for export] *)
                              (
                               PX XMemset []  (* [comment removed for export] *)
                               (
                                PRun []  (* [comment removed for export] *)
                                (
                                 PX XMemset []  (* [comment removed for export] *)
                                 (
                                  PRun []  (* [comment removed for export] *)
                                  (
                                   PX XMemset []  (* [comment removed for export] *)
                                   (
                                    PRun []  (* [comment removed for export] *)
                                    (
                                     PX XMemset []  (* [comment removed for export] *)
                                     (
                                      PRun []  (* [comment removed for export] *)
                                      (
                                       PX XMemset []  (* [comment removed for export] *)
                                       (
                                        PRun []  (* [comment removed for export] *)
                                        (
                                         PX XMemset []  (* [comment removed for export] *)
                                         (
                                          PRun []  (* [comment removed for export] *)
                                          (
                                           PX XMemset []  (* [comment removed for export] *)
                                           (
                                            PRun []  (* [comment removed for export] *)
                                            (
                                             PX XMemset []  (* [comment removed for export] *)
                                             (
                                              PRun []  (* [comment removed for export] *)
                                              (
                                               PX XMemset []  (* [comment removed for export] *)
                                               (
                                                PRun []  (* [comment removed for export] *)
                                                (
                                                 PX XMemset []  (* [comment removed for export] *)
                                                 (
                                                  PRun []  (* [comment removed for export] *)
                                                  (
                                                   PX XMemset []  (* [comment removed for export] *)
                                                   (
                                                    PRun []  (* [comment removed for export] *)
                                                    (
                                                     PX XMemset []  (* [comment removed for export] *)
                                                     (
                                                      PRun []  (* [comment removed for export] *)
                                                      (
                                                       PX XMemset []  (* [comment removed for export] *)
                                                       (
                                                        PRun []  (* [comment removed for export] *)
                                                        (
                                                         PX XMemset []  (* [comment removed for export] *)
                                                         (
                                                          PRun []  (* [comment removed for export] *)
                                                          (
                                                           PX XMemset []  (* [comment removed for export] *)
                                                           (
                                                            PRun []  (* [comment removed for export] *)
                                                            (
                                                             PX XMemset []  (* [comment removed for export] *)
                                                             (
                                                              PRun []  (* [comment removed for export] *)
                                                              (
                                                               PX XMemset []  (* [comment removed for export] *)
                                                               (
                                                                PRun []  (* [comment removed for export] *)
                                                                (
                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                 (
                                                                  PRun []  (* [comment removed for export] *)
                                                                  (
                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                   (
                                                                    PRun []  (* [comment removed for export] *)
                                                                    (
                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                     (
                                                                      PRun []  (* [comment removed for export] *)
                                                                      (
                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                       (
                                                                        PRun []  (* [comment removed for export] *)
                                                                        (
                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                         (
                                                                          PRun []  (* [comment removed for export] *)
                                                                          (
                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                           (
                                                                            PRun []  (* [comment removed for export] *)
                                                                            (
                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                             (
                                                                              PRun []  (* [comment removed for export] *)
                                                                              (
                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                               (
                                                                                PRun []  (* [comment removed for export] *)
                                                                                (
                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                 (
                                                                                  PRun []  (* [comment removed for export] *)
                                                                                  (
                                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun []  (* [comment removed for export] *)
                                                                                    (
                                                                                     PMmap  (* [comment removed for export] *)
                                                                                     (
                                                                                      PSpin  (* [comment removed for export] *))
                                                                                     (
                                                                                      PShDisj (escale 4096 (EVar 591)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                      (
                                                                                       PShDisj (escale 4096 (EVar 591)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun []  (* [comment removed for export] *)
                                                                                        (
                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun []  (* [comment removed for export] *)
                                                                                          (
                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun []  (* [comment removed for export] *)
                                                                                            (
                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                             (
                                                                                              PRun [0x81418]  (* [comment removed for export] *)
                                                                                              (
                                                                                               PHandoff 3000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_via_U_slice (r : Z) : plan :=
  PRun []  (* [comment removed for export] *)
  (
   (* LPS 75d69e00 (#38).  [startup_plan_via_U_slice] is the else-arm twin of
      [startup_plan_via_U] above and joins the SAME snapshot shape ([js_3] is [js_0]
      but for [a_abytes]), so it needs the SAME variable correspondence.  It did not
      carry one: before the [startup_plan_hmset10] repair the walk refused at that
      arm's [PShDisj] and never reached this [PVia], so the omission was invisible.
      With the arm open, [via_ok] refuses here -- mask 23 of 31, the one failing
      conjunct being [nxt cs <= lo] with nxt cs 445 against lo 185 -- and the 25 live
      variables the walk carries at this node are EXACTLY the 25 sources of the
      [PRename] at line 474, measured by set equality in both directions, which is
      why the same map serves here.  Renaming is what brings [nxt] back down:
      [node_rename] sets it to [Nat.max gb (csmaxv cs)] ([AsanPlanCore.v:3307]), so
      after the map the counter is the largest renamed index, not 445.  Raising [lo]
      instead would clear [via_ok] and then fail the [PMerge]'s [entails_h], because
      [js_3]'s rigid rows name the RENAMED variables. *)
   PRename [(47, 12); (48, 13); (81, 14); (210, 15); (227, 16); (228, 17); (20, 18); (246, 19); (247, 20); (21, 21); (361, 22); (362, 23); (395, 28); (428, 61); (430, 29); (431, 30); (432, 31); (436, 32); (437, 33); (438, 34); (439, 35); (441, 36); (442, 37); (443, 38); (444, 39)]%nat  (* [comment removed for export] *)
   (
   PVia 3 (js_3 r) 185  (* [comment removed for export] *)
   (
    PBrk2S  (* [comment removed for export] *)
    (
     startup_plan_viafail6)
    (
     PRun []  (* [comment removed for export] *)
     (
      PMmapIn  (* [comment removed for export] *)
      (
       PSpin  (* [comment removed for export] *))
      (
       PRun []  (* [comment removed for export] *)
       (
        PBump 86  (* [comment removed for export] *)
        (
         PIntroW 4295491576 [KRange (EVar 86) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 86)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6348800) (SA (escale 4096 (EVar 86)) 0) (ELit 8192)]  (* [comment removed for export] *)
         (
          PGhost (eaddz (escale 4096 (EVar 86)) 4096) (ELit 4096)  (* [comment removed for export] *)
          (
           PMmap  (* [comment removed for export] *)
           (
            PSpin  (* [comment removed for export] *))
           (
            PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
            (
             PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
             (
              PRun []  (* [comment removed for export] *)
              (
               PX XIMemset []  (* [comment removed for export] *)
               (
                PRun []  (* [comment removed for export] *)
                (
                 PX XIMemset []  (* [comment removed for export] *)
                 (
                  PBump 184  (* [comment removed for export] *)
                  (
                   PFog 1 8192  (* [comment removed for export] *)
                   (
                    PShDisj (escale 4096 (EVar 61)) (ELit 0xb09000) (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                    (
                     PUnvis (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                     (
                      PHavocBrk 0x61e000 0x80620000  (* [comment removed for export] *)
                      (
                       PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat  (* [comment removed for export] *)
                       (
                        PMerge 3  (* [comment removed for export] *)))))))))))))))))))
      (
       PSpin  (* [comment removed for export] *)))))
   (
    PRename [(28, 24); (61, 25); (86, 26); (87, 27); (184, 28); (185, 29); (186, 30); (187, 31); (188, 32); (189, 33); (190, 34); (191, 35); (192, 36); (193, 37); (194, 38); (195, 39); (196, 40); (197, 41); (198, 42); (199, 43)]%nat  (* [comment removed for export] *)
    (
     PCase2 (esub (eaddz (escale 16 (EVar 6)) 36703) (escale 4096 (EVar 24))) 4030  (* [comment removed for export] *)
     (
      startup_plan_tail7)
     (
      startup_plan_tail8))))).

Definition startup_plan_hmset9 (r : Z) : plan :=
  PX XMemset []  (* [comment removed for export] *)
  (
   PRun []  (* [comment removed for export] *)
   (
    PX XMemset []  (* [comment removed for export] *)
    (
     PRun []  (* [comment removed for export] *)
     (
      PMmap  (* [comment removed for export] *)
      (
       PSpin  (* [comment removed for export] *))
      (
       PShDisj (escale 4096 (EVar 428)) (ELit 0xb09000) e_band e_bandlen  (* [comment removed for export] *)
       (
        PShDisj (escale 4096 (EVar 428)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
        (
         PRun []  (* [comment removed for export] *)
         (
          PX XMemcpy []  (* [comment removed for export] *)
          (
           PRun []  (* [comment removed for export] *)
           (
            PSys YBrk  (* [comment removed for export] *)
            (
             startup_plan_via_U r))))))))))).

(* LPS 75d69e00 (#38).  [startup_plan_hmset10] is the else arm of the [PCase2] in
   [startup_plan_s2U11] below; [startup_plan_hmset9] is the then arm.  Both arms
   [PMmap] the same 0xb09000 region at the same point of the walk, so the walk's
   fresh counter is the same in both and the two arms must name the same variable.
   The then arm names [EVar 428]; this arm still named [EVar 61], a literal left
   over from the pre-revision numbering (61 is a renamed slot, see the [PRename]
   above).  Under #38 that is the refusal the farm printed:
     CErr 3 at pc 415128, nxt 429, failing node constructor PShDisj,
     conjunct mask 687 of 2047 (flat c1, flat shadow 1, shd_end 1 and
     ranges_apart all fail), plan names variable 61 where the largest v with
     [flat_xB] of [escale 4096 (EVar v)] at this node's own length is 428.
   428 is MEASURED at this node, not extrapolated, and it is the same value the
   sibling arm already carries.  Both CONFIG_RSEQ arms printed the identical
   tuple, so the flag stays free and nothing here is pinned. *)
Definition startup_plan_hmset10 (r : Z) : plan :=
  PX XMemset []  (* [comment removed for export] *)
  (
   PDropRange (eaddz (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 395))) 2146398208) (eaddz (esub (escale 2 (EVar 6)) (escale 512 (EVar 395))) 4096)  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PX XMemset []  (* [comment removed for export] *)
     (
      PRun []  (* [comment removed for export] *)
      (
       PMmap  (* [comment removed for export] *)
       (
        PSpin  (* [comment removed for export] *))
       (
        PShDisj (escale 4096 (EVar 428)) (ELit 0xb09000) e_band e_bandlen  (* [comment removed for export] *)
        (
         PShDisj (escale 4096 (EVar 428)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
         (
          PRun []  (* [comment removed for export] *)
          (
           PX XMemcpy []  (* [comment removed for export] *)
           (
            PRun []  (* [comment removed for export] *)
            (
             PSys YBrk  (* [comment removed for export] *)
             (
              startup_plan_via_U_slice r)))))))))))).

Definition startup_plan_s2U11 (r : Z) : plan :=
  PRun [0x6d734]  (* [comment removed for export] *)
  (
   PFresh 10 12 (Some (eaddz (escale 32768 (EVar 0)) (-32768)))  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PCase2 (esub (eaddz (escale 2 (EVar 6)) 11776) (escale 512 (EVar 395))) 7679  (* [comment removed for export] *)
     (
      startup_plan_hmset9 r)
     (
      PVisSlice (eadd (escale 32768 (EVar 0)) (eaddz (escale 4096 (EVar 395)) (-8421376))) (esub e_band (eadd (escale 32768 (EVar 0)) (eaddz (escale 4096 (EVar 395)) (-8421376))))  (* [comment removed for export] *)
      (
       startup_plan_hmset10 r))))).

(* LPS 75d69e00 (#38): the plan is indexed by the run's CONFIG_RSEQ flag, as
   [K/A/TopA.v:149] and [K/A/TopA_start.v:225] already state
   ([startup_plan : Z -> plan]); the certificate is one per value of the flag and
   the case split happens where it is discharged, on closed goals
   ([K/A/TopA_start.v:76-77]).  The PLAN TEXT below is UNCHANGED: at this revision
   the flag reaches the walk only through [check]'s own [rz] argument, which
   [node_pnscan] / [node_layout] read ([AsanPlan.v:29-31]), not through the plan's
   nodes. *)
Definition startup_plan (r : Z) : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PX XIMemset []  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PX XEnvScan []  (* [comment removed for export] *)
     (
      PRun []  (* [comment removed for export] *)
      (
       PX XPnScan []  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PX XIMemcpy []  (* [comment removed for export] *)
         (
          PRun []  (* [comment removed for export] *)
          (
           PSys YSetTid  (* [comment removed for export] *)
           (
            PRun []  (* [comment removed for export] *)
            (
             PRun [0xaf020]  (* [comment removed for export] *)
             (
              PHavocCell (ELit 0x61c118) 8  (* [comment removed for export] *)
              (
               PRun [0x663d8]  (* [comment removed for export] *)
               (
                PX XSniff []  (* [comment removed for export] *)
                (
                 PRun []  (* [comment removed for export] *)
                 (
                  PMmap  (* [comment removed for export] *)
                  (
                   PSpin  (* [comment removed for export] *))
                  (
                   PRun []  (* [comment removed for export] *)
                   (
                    PMmap  (* [comment removed for export] *)
                    (
                     PSpin  (* [comment removed for export] *))
                    (
                     PRun []  (* [comment removed for export] *)
                     (
                      PMmap  (* [comment removed for export] *)
                      (
                       PSpin  (* [comment removed for export] *))
                      (
                       PRun [0x651bc]  (* [comment removed for export] *)
                       (
                        PX XIStrncpy []  (* [comment removed for export] *)
                        (
                         PRun [0x651bc]  (* [comment removed for export] *)
                         (
                          PX XIStrncpy []  (* [comment removed for export] *)
                          (
                           PRun []  (* [comment removed for export] *)
                           (
                            PMmap  (* [comment removed for export] *)
                            (
                             PSpin  (* [comment removed for export] *))
                            (
                             PShDisj (escale 4096 (EVar 81)) (ELit 0x10000) e_band e_bandlen  (* [comment removed for export] *)
                             (
                              PShDisj (escale 4096 (EVar 81)) (ELit 0x10000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                              (
                               PRun []  (* [comment removed for export] *)
                               (
                                PX XIMemset []  (* [comment removed for export] *)
                                (
                                 PRun []  (* [comment removed for export] *)
                                 (
                                  PX XIMemcpy []  (* [comment removed for export] *)
                                  (
                                   PRun []  (* [comment removed for export] *)
                                   (
                                    PX XIMemcpy []  (* [comment removed for export] *)
                                    (
                                     PRun [0x649d4]  (* [comment removed for export] *)
                                     (
                                      PRun [0x649d4]  (* [comment removed for export] *)
                                      (
                                       PRun [0x649d4]  (* [comment removed for export] *)
                                       (
                                        PRun [0x649d4]  (* [comment removed for export] *)
                                        (
                                         PRun [0x649d4]  (* [comment removed for export] *)
                                         (
                                          PRun [0x649d4]  (* [comment removed for export] *)
                                          (
                                           PRun [0x649d4]  (* [comment removed for export] *)
                                           (
                                            PRun [0x649d4]  (* [comment removed for export] *)
                                            (
                                             PRun [0x649d4]  (* [comment removed for export] *)
                                             (
                                              PRun [0x649d4]  (* [comment removed for export] *)
                                              (
                                               PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                               (
                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                (
                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                 (
                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                  (
                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                   (
                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                    (
                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                     (
                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                      (
                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                       (
                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                        (
                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                         (
                                                          PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                          (
                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                           (
                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                            (
                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                             (
                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                              (
                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                               (
                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                (
                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                 (
                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                  (
                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                   (
                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                    (
                                                                     PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                     (
                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                      (
                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                       (
                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                        (
                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                         (
                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                          (
                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                           (
                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                            (
                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                             (
                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                              (
                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                               (
                                                                                PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                (
                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                 (
                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                  (
                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                    (
                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                     (
                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                      (
                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                        (
                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                          (
                                                                                           PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                            (
                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                             (
                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                              (
                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                               (
                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                (
                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                 (
                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                  (
                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                   (
                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                    (
                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                     (
                                                                                                      PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                      (
                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                       (
                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                        (
                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                         (
                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                          (
                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                           (
                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                            (
                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                             (
                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                              (
                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                               (
                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                (
                                                                                                                 PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                 (
                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                  (
                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                   (
                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                    (
                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                     (
                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                      (
                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                       (
                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                        (
                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                         (
                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                          (
                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                           (
                                                                                                                            PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                            (
                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                             (
                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                              (
                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                               (
                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                (
                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                 (
                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                  (
                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                   (
                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                    (
                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                     (
                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                      (
                                                                                                                                       PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                       (
                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                        (
                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                         (
                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                          (
                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                           (
                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                            (
                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                             (
                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                              (
                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                               (
                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                (
                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                 (
                                                                                                                                                  PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                  (
                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                   (
                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                    (
                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                     (
                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                      (
                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                       (
                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                        (
                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                         (
                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                          (
                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                           (
                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                            (
                                                                                                                                                             PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                             (
                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                              (
                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                               (
                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                (
                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                 (
                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                  (
                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                   (
                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                    (
                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                     (
                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                      (
                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                       (
                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                        (
                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                         (
                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                          (
                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                           (
                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                            (
                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                             (
                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                              (
                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                               (
                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                (
                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                 (
                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                  (
                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                   (
                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                    (
                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                     (
                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                      (
                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                       (
                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                        (
                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                         (
                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                           (
                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                            (
                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                             (
                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                              (
                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                               (
                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                (
                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                 (
                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                  (
                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                   (
                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                    (
                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                     (
                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                       (
                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                        (
                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                         (
                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                          (
                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                           (
                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                            (
                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                             (
                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                              (
                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                               (
                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                (
                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                 (
                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                  (
                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                   (
                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                    (
                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                     (
                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                       (
                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                        (
                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                         (
                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                          (
                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                           (
                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                            (
                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                              (
                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                          PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                     PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                           PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                      PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                 PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                            PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                       PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                  PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                             PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                    PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                               PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                         PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x649d4]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                    PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                     PX XIMemcpy []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                      PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                       PX XIMemcpy []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                         PX XIMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                           PX XIMemcpy []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                             PX XIMemcpy []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x5a7f8]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                               PDropRange (escale 4096 (EVar 81)) (ELit 0x10000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x663d8]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                 PX XSniff []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                  PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                   PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                    PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                    PShDisj (escale 4096 (EVar 210)) (ELit 0x38e000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 210)) (ELit 0x38e000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x528a0]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                       PX XHeapSort []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                         PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                          PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                          PShDisj (escale 4096 (EVar 227)) (ELit 0x2000011000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                           PShDisj (escale 4096 (EVar 227)) (ELit 0x2000011000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                            PDropRange (ELit 0xc6a38) (ELit 0x12b0)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x6d200]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                              PFresh 9 12 None  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                                               PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                                PMmapIn  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                 PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                 PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                                  PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                                   PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                                    PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                     PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 245)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 245)) (ELit 0x800000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                                       PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                                        PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PShDisj (escale 4096 (EVar 246)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                                          PShDisj (escale 4096 (EVar 246)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                                           PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                                            PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PShDisj (escale 4096 (EVar 247)) (ELit 0x10000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                              PShDisj (escale 4096 (EVar 247)) (ELit 0x10000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                                                               PCaseDisjJ (ELit 0x7fff7000) (escale 4096 (EVar 247)) 0x54e7c []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                PBump 278  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                 PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 294)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 294)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        PX XIMemcpy []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          PX XIMemcpy []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            PX XMemIsZero []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 PShDisj (escale 4096 (EVar 361)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  PShDisj (escale 4096 (EVar 361)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 362)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 362)) (ELit 0x1000) (ELit 0x10000) (ELit 0x60e000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        PX XIMemcpy []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          PX XIMemcpy []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            PSys YMunmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             PRename [(45, 12); (46, 13); (79, 14); (208, 15); (225, 16); (226, 17); (243, 18); (244, 19); (245, 20); (294, 21); (359, 22); (360, 23); (389, 24); (390, 25); (391, 26); (392, 27)]%nat  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              startup_plan_s2U11 r))))))))))))))))))))))))))))))))))))))))))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                 PSpin  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_ranges : list (Z * nat) := [(0x31700, 384%nat); (0x33a00, 512%nat); (0x34c00, 192%nat); (0x38200, 192%nat); (0x38800, 192%nat); (0x3d500, 128%nat); (0x3dc00, 192%nat); (0x3e600, 1088%nat); (0x3fd00, 960%nat); (0x41100, 192%nat); (0x41900, 256%nat); (0x41e00, 640%nat); (0x43100, 192%nat); (0x47c00, 192%nat); (0x48c00, 256%nat); (0x49b00, 6784%nat); (0x52800, 192%nat); (0x53000, 448%nat); (0x53900, 384%nat); (0x54100, 128%nat); (0x54b00, 512%nat); (0x55500, 256%nat); (0x55c00, 320%nat); (0x59a00, 192%nat); (0x5a200, 128%nat); (0x5a700, 640%nat); (0x5b200, 512%nat); (0x5c300, 384%nat); (0x5cc00, 320%nat); (0x5d200, 832%nat); (0x5ed00, 320%nat); (0x5f500, 256%nat); (0x60d00, 192%nat); (0x61400, 128%nat); (0x61700, 128%nat); (0x61b00, 128%nat); (0x61e00, 256%nat); (0x62600, 256%nat); (0x62b00, 1344%nat); (0x64200, 640%nat); (0x64d00, 640%nat); (0x65800, 128%nat); (0x66300, 192%nat); (0x66700, 256%nat); (0x66c00, 256%nat); (0x67100, 320%nat); (0x67900, 960%nat); (0x69c00, 512%nat); (0x6a800, 832%nat); (0x6bc00, 384%nat); (0x6c800, 256%nat); (0x6d100, 192%nat); (0x6d500, 704%nat); (0x6e200, 384%nat); (0x6ea00, 320%nat); (0x6f300, 320%nat); (0x70e00, 128%nat); (0x71200, 320%nat); (0x71d00, 192%nat); (0x73500, 512%nat); (0x74000, 320%nat); (0x74800, 192%nat); (0x7b300, 384%nat); (0x7ba00, 128%nat); (0x7e200, 128%nat); (0x81100, 320%nat); (0x81b00, 128%nat); (0xae600, 896%nat); (0xaf600, 192%nat); (0xafe00, 128%nat); (0xb0500, 1152%nat); (0xb3a00, 192%nat); (0xb8d00, 384%nat); (0xb9500, 384%nat); (0xba900, 128%nat); (0xbad00, 512%nat); (0xbb900, 128%nat)]%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
