(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z Z2y.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z10f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition startup_plan_wsplit1 : plan :=
  PRun []
  (
   PMprotect
   (
    PSpin   )
   (
    PRun []
    (
     PMmap
     (
      PSpin   )
     (
      PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen
      (
       PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
       (
        PRun []
        (
         PX XIMemset []
         (
          PRun []
          (
           PX XIMemset []
           (
            PBump 182
            (
             PFog 1 8192
             (
              PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)
              (
               PUnvis (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)
               (
                PGhost (escale 4096 (EVar 5)) (ELit 8192)
                (
                 PHavocBrk 0x676000 0x80678000
                 (
                  PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
                  (
                   PMerge 0   ))))))))))))))))).

Definition startup_plan_viafail2 : plan :=
  PRun []
  (
   PBump 84
   (
    PMmap
    (
     PSpin   )
    (
     PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) e_band e_bandlen
     (
      PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) (ELit 0x10000) (ELit 0x666000)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 84))
       (
        startup_plan_wsplit1)
       (
        startup_plan_wsplit1)))))).

Definition startup_plan_tail3 : plan :=
  PRun [0x531ac]
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8
   (
    PRun []
    (
     PMmap
     (
      PSpin   )
     (
      PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) e_band e_bandlen
      (
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x666000)
       (
        PRun []
        (
         PMmap
         (
          PSpin   )
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x666000)
           (
            PRun []
            (
             PX XIMemcpy []
             (
              PRun []
              (
               PMmap
               (
                PSpin   )
               (
                PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) e_band e_bandlen
                (
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                 (
                  PRun []
                  (
                   PX XIMemcpy []
                   (
                    PRun []
                    (
                     PX XIMemcpy []
                     (
                      PRun []
                      (
                       PX XMemset []
                       (
                        PRun []
                        (
                         PX XMemset []
                         (
                          PRun []
                          (
                           PX XMemset []
                           (
                            PRun []
                            (
                             PX XMemset []
                             (
                              PRun []
                              (
                               PX XMemset []
                               (
                                PRun []
                                (
                                 PX XMemset []
                                 (
                                  PRun []
                                  (
                                   PX XMemset []
                                   (
                                    PRun []
                                    (
                                     PMmap
                                     (
                                      PSpin   )
                                     (
                                      PShDisj (escale 4096 (EVar 205)) (ELit 0x1000) e_band e_bandlen
                                      (
                                       PShDisj (escale 4096 (EVar 205)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                                       (
                                        PRun []
                                        (
                                         PX XMemset []
                                         (
                                          PRun []
                                          (
                                           PX XMemset []
                                           (
                                            PRun []
                                            (
                                             PX XMemset []
                                             (
                                              PRun []
                                              (
                                               PX XMemset []
                                               (
                                                PRun []
                                                (
                                                 PX XMemset []
                                                 (
                                                  PRun []
                                                  (
                                                   PX XMemset []
                                                   (
                                                    PRun []
                                                    (
                                                     PX XMemset []
                                                     (
                                                      PRun []
                                                      (
                                                       PX XMemset []
                                                       (
                                                        PRun []
                                                        (
                                                         PX XMemset []
                                                         (
                                                          PRun []
                                                          (
                                                           PX XMemset []
                                                           (
                                                            PRun []
                                                            (
                                                             PX XMemset []
                                                             (
                                                              PRun []
                                                              (
                                                               PX XMemset []
                                                               (
                                                                PRun []
                                                                (
                                                                 PX XMemset []
                                                                 (
                                                                  PRun []
                                                                  (
                                                                   PX XMemset []
                                                                   (
                                                                    PRun []
                                                                    (
                                                                     PX XMemset []
                                                                     (
                                                                      PRun []
                                                                      (
                                                                       PX XMemset []
                                                                       (
                                                                        PRun []
                                                                        (
                                                                         PX XMemset []
                                                                         (
                                                                          PRun []
                                                                          (
                                                                           PX XMemset []
                                                                           (
                                                                            PRun []
                                                                            (
                                                                             PX XMemset []
                                                                             (
                                                                              PRun []
                                                                              (
                                                                               PX XMemset []
                                                                               (
                                                                                PRun []
                                                                                (
                                                                                 PX XMemset []
                                                                                 (
                                                                                  PRun []
                                                                                  (
                                                                                   PX XMemset []
                                                                                   (
                                                                                    PRun []
                                                                                    (
                                                                                     PX XMemset []
                                                                                     (
                                                                                      PRun []
                                                                                      (
                                                                                       PX XMemset []
                                                                                       (
                                                                                        PRun []
                                                                                        (
                                                                                         PX XMemset []
                                                                                         (
                                                                                          PRun []
                                                                                          (
                                                                                           PX XMemset []
                                                                                           (
                                                                                            PRun []
                                                                                            (
                                                                                             PX XMemset []
                                                                                             (
                                                                                              PRun []
                                                                                              (
                                                                                               PX XMemset []
                                                                                               (
                                                                                                PRun []
                                                                                                (
                                                                                                 PX XMemset []
                                                                                                 (
                                                                                                  PRun []
                                                                                                  (
                                                                                                   PX XMemset []
                                                                                                   (
                                                                                                    PRun [0x96610]
                                                                                                    (
                                                                                                     PHandoff 0   ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail4 : plan :=
  PRun [0x531ac]
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8
   (
    PRun []
    (
     PMmap
     (
      PSpin   )
     (
      PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) e_band e_bandlen
      (
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x666000)
       (
        PRun []
        (
         PMmap
         (
          PSpin   )
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x666000)
           (
            PRun []
            (
             PX XIMemcpy []
             (
              PRun []
              (
               PMmap
               (
                PSpin   )
               (
                PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) e_band e_bandlen
                (
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                 (
                  PRun []
                  (
                   PX XIMemcpy []
                   (
                    PRun []
                    (
                     PX XIMemcpy []
                     (
                      PRun []
                      (
                       PX XMemset []
                       (
                        PRun []
                        (
                         PX XMemset []
                         (
                          PRun []
                          (
                           PX XMemset []
                           (
                            PRun []
                            (
                             PX XMemset []
                             (
                              PRun []
                              (
                               PX XMemset []
                               (
                                PRun []
                                (
                                 PX XMemset []
                                 (
                                  PRun []
                                  (
                                   PX XMemset []
                                   (
                                    PRun []
                                    (
                                     PMmap
                                     (
                                      PSpin   )
                                     (
                                      PShDisj (escale 4096 (EVar 205)) (ELit 0x1000) e_band e_bandlen
                                      (
                                       PShDisj (escale 4096 (EVar 205)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                                       (
                                        PRun []
                                        (
                                         PX XMemset []
                                         (
                                          PRun []
                                          (
                                           PX XMemset []
                                           (
                                            PRun []
                                            (
                                             PX XMemset []
                                             (
                                              PRun []
                                              (
                                               PX XMemset []
                                               (
                                                PRun []
                                                (
                                                 PX XMemset []
                                                 (
                                                  PRun []
                                                  (
                                                   PX XMemset []
                                                   (
                                                    PRun []
                                                    (
                                                     PX XMemset []
                                                     (
                                                      PRun []
                                                      (
                                                       PX XMemset []
                                                       (
                                                        PRun []
                                                        (
                                                         PX XMemset []
                                                         (
                                                          PRun []
                                                          (
                                                           PX XMemset []
                                                           (
                                                            PRun []
                                                            (
                                                             PX XMemset []
                                                             (
                                                              PRun []
                                                              (
                                                               PX XMemset []
                                                               (
                                                                PRun []
                                                                (
                                                                 PX XMemset []
                                                                 (
                                                                  PRun []
                                                                  (
                                                                   PX XMemset []
                                                                   (
                                                                    PRun []
                                                                    (
                                                                     PX XMemset []
                                                                     (
                                                                      PRun []
                                                                      (
                                                                       PX XMemset []
                                                                       (
                                                                        PRun []
                                                                        (
                                                                         PX XMemset []
                                                                         (
                                                                          PRun []
                                                                          (
                                                                           PX XMemset []
                                                                           (
                                                                            PRun []
                                                                            (
                                                                             PX XMemset []
                                                                             (
                                                                              PRun []
                                                                              (
                                                                               PX XMemset []
                                                                               (
                                                                                PRun []
                                                                                (
                                                                                 PX XMemset []
                                                                                 (
                                                                                  PRun []
                                                                                  (
                                                                                   PX XMemset []
                                                                                   (
                                                                                    PRun []
                                                                                    (
                                                                                     PX XMemset []
                                                                                     (
                                                                                      PRun []
                                                                                      (
                                                                                       PX XMemset []
                                                                                       (
                                                                                        PRun []
                                                                                        (
                                                                                         PX XMemset []
                                                                                         (
                                                                                          PRun []
                                                                                          (
                                                                                           PX XMemset []
                                                                                           (
                                                                                            PRun []
                                                                                            (
                                                                                             PX XMemset []
                                                                                             (
                                                                                              PRun []
                                                                                              (
                                                                                               PX XMemset []
                                                                                               (
                                                                                                PRun []
                                                                                                (
                                                                                                 PX XMemset []
                                                                                                 (
                                                                                                  PRun []
                                                                                                  (
                                                                                                   PX XMemset []
                                                                                                   (
                                                                                                    PRun [0x96610]
                                                                                                    (
                                                                                                     PHandoff 1000   ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_via_U : plan :=
  PRun []
  (
   PVia 0 js_0 183
   (
    PBrk2S
    (
     startup_plan_viafail2)
    (
     PRun []
     (
      PMmapIn
      (
       PSpin   )
      (
       PRun []
       (
        PBump 84
        (
         PIntroW 4295491576 [KRange (EVar 84) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 84)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6709248) (SA (escale 4096 (EVar 84)) 0) (ELit 8192)]
         (
          PGhost (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)
          (
           PMmap
           (
            PSpin   )
           (
            PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen
            (
             PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
             (
              PRun []
              (
               PX XIMemset []
               (
                PRun []
                (
                 PX XIMemset []
                 (
                  PBump 182
                  (
                   PFog 1 8192
                   (
                    PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (escale 4096 (EVar 5)) (ELit 8192)
                    (
                     PUnvis (escale 4096 (EVar 5)) (ELit 8192)
                     (
                      PHavocBrk 0x676000 0x80678000
                      (
                       PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
                       (
                        PMerge 0   ))))))))))))))))))
      (
       PSpin   ))))
   (
    PRename [(26, 22); (59, 23); (84, 24); (85, 25); (182, 26); (183, 27); (184, 28); (185, 29); (186, 30); (187, 31); (188, 32); (189, 33); (190, 34); (191, 35); (192, 36); (193, 37); (194, 38); (195, 39); (196, 40); (197, 41)]%nat
    (
     PCase2 (esub (eaddz (escale 16 (EVar 6)) 36703) (escale 4096 (EVar 22))) 4030
     (
      startup_plan_tail3)
     (
      startup_plan_tail4)))).

Definition startup_plan_wsplit5 : plan :=
  PRun []
  (
   PMprotect
   (
    PSpin   )
   (
    PRun []
    (
     PMmap
     (
      PSpin   )
     (
      PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen
      (
       PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
       (
        PRun []
        (
         PX XIMemset []
         (
          PRun []
          (
           PX XIMemset []
           (
            PBump 182
            (
             PFog 1 8192
             (
              PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)
              (
               PUnvis (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)
               (
                PGhost (escale 4096 (EVar 5)) (ELit 8192)
                (
                 PHavocBrk 0x676000 0x80678000
                 (
                  PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
                  (
                   PMerge 3   ))))))))))))))))).

Definition startup_plan_viafail6 : plan :=
  PRun []
  (
   PBump 84
   (
    PMmap
    (
     PSpin   )
    (
     PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) e_band e_bandlen
     (
      PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) (ELit 0x10000) (ELit 0x666000)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 84))
       (
        startup_plan_wsplit5)
       (
        startup_plan_wsplit5)))))).

Definition startup_plan_tail7 : plan :=
  PRun [0x531ac]
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8
   (
    PRun []
    (
     PMmap
     (
      PSpin   )
     (
      PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) e_band e_bandlen
      (
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x666000)
       (
        PRun []
        (
         PMmap
         (
          PSpin   )
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x666000)
           (
            PRun []
            (
             PX XIMemcpy []
             (
              PRun []
              (
               PMmap
               (
                PSpin   )
               (
                PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) e_band e_bandlen
                (
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                 (
                  PRun []
                  (
                   PX XIMemcpy []
                   (
                    PRun []
                    (
                     PX XIMemcpy []
                     (
                      PRun []
                      (
                       PX XMemset []
                       (
                        PRun []
                        (
                         PX XMemset []
                         (
                          PRun []
                          (
                           PX XMemset []
                           (
                            PRun []
                            (
                             PX XMemset []
                             (
                              PRun []
                              (
                               PX XMemset []
                               (
                                PRun []
                                (
                                 PX XMemset []
                                 (
                                  PRun []
                                  (
                                   PX XMemset []
                                   (
                                    PRun []
                                    (
                                     PMmap
                                     (
                                      PSpin   )
                                     (
                                      PShDisj (escale 4096 (EVar 205)) (ELit 0x1000) e_band e_bandlen
                                      (
                                       PShDisj (escale 4096 (EVar 205)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                                       (
                                        PRun []
                                        (
                                         PX XMemset []
                                         (
                                          PRun []
                                          (
                                           PX XMemset []
                                           (
                                            PRun []
                                            (
                                             PX XMemset []
                                             (
                                              PRun []
                                              (
                                               PX XMemset []
                                               (
                                                PRun []
                                                (
                                                 PX XMemset []
                                                 (
                                                  PRun []
                                                  (
                                                   PX XMemset []
                                                   (
                                                    PRun []
                                                    (
                                                     PX XMemset []
                                                     (
                                                      PRun []
                                                      (
                                                       PX XMemset []
                                                       (
                                                        PRun []
                                                        (
                                                         PX XMemset []
                                                         (
                                                          PRun []
                                                          (
                                                           PX XMemset []
                                                           (
                                                            PRun []
                                                            (
                                                             PX XMemset []
                                                             (
                                                              PRun []
                                                              (
                                                               PX XMemset []
                                                               (
                                                                PRun []
                                                                (
                                                                 PX XMemset []
                                                                 (
                                                                  PRun []
                                                                  (
                                                                   PX XMemset []
                                                                   (
                                                                    PRun []
                                                                    (
                                                                     PX XMemset []
                                                                     (
                                                                      PRun []
                                                                      (
                                                                       PX XMemset []
                                                                       (
                                                                        PRun []
                                                                        (
                                                                         PX XMemset []
                                                                         (
                                                                          PRun []
                                                                          (
                                                                           PX XMemset []
                                                                           (
                                                                            PRun []
                                                                            (
                                                                             PX XMemset []
                                                                             (
                                                                              PRun []
                                                                              (
                                                                               PX XMemset []
                                                                               (
                                                                                PRun []
                                                                                (
                                                                                 PX XMemset []
                                                                                 (
                                                                                  PRun []
                                                                                  (
                                                                                   PX XMemset []
                                                                                   (
                                                                                    PRun []
                                                                                    (
                                                                                     PX XMemset []
                                                                                     (
                                                                                      PRun []
                                                                                      (
                                                                                       PX XMemset []
                                                                                       (
                                                                                        PRun []
                                                                                        (
                                                                                         PX XMemset []
                                                                                         (
                                                                                          PRun []
                                                                                          (
                                                                                           PX XMemset []
                                                                                           (
                                                                                            PRun []
                                                                                            (
                                                                                             PX XMemset []
                                                                                             (
                                                                                              PRun []
                                                                                              (
                                                                                               PX XMemset []
                                                                                               (
                                                                                                PRun []
                                                                                                (
                                                                                                 PX XMemset []
                                                                                                 (
                                                                                                  PRun []
                                                                                                  (
                                                                                                   PX XMemset []
                                                                                                   (
                                                                                                    PRun [0x96610]
                                                                                                    (
                                                                                                     PHandoff 2000   ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail8 : plan :=
  PRun [0x531ac]
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8
   (
    PRun []
    (
     PMmap
     (
      PSpin   )
     (
      PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) e_band e_bandlen
      (
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x666000)
       (
        PRun []
        (
         PMmap
         (
          PSpin   )
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x666000)
           (
            PRun []
            (
             PX XIMemcpy []
             (
              PRun []
              (
               PMmap
               (
                PSpin   )
               (
                PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) e_band e_bandlen
                (
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                 (
                  PRun []
                  (
                   PX XIMemcpy []
                   (
                    PRun []
                    (
                     PX XIMemcpy []
                     (
                      PRun []
                      (
                       PX XMemset []
                       (
                        PRun []
                        (
                         PX XMemset []
                         (
                          PRun []
                          (
                           PX XMemset []
                           (
                            PRun []
                            (
                             PX XMemset []
                             (
                              PRun []
                              (
                               PX XMemset []
                               (
                                PRun []
                                (
                                 PX XMemset []
                                 (
                                  PRun []
                                  (
                                   PX XMemset []
                                   (
                                    PRun []
                                    (
                                     PMmap
                                     (
                                      PSpin   )
                                     (
                                      PShDisj (escale 4096 (EVar 205)) (ELit 0x1000) e_band e_bandlen
                                      (
                                       PShDisj (escale 4096 (EVar 205)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                                       (
                                        PRun []
                                        (
                                         PX XMemset []
                                         (
                                          PRun []
                                          (
                                           PX XMemset []
                                           (
                                            PRun []
                                            (
                                             PX XMemset []
                                             (
                                              PRun []
                                              (
                                               PX XMemset []
                                               (
                                                PRun []
                                                (
                                                 PX XMemset []
                                                 (
                                                  PRun []
                                                  (
                                                   PX XMemset []
                                                   (
                                                    PRun []
                                                    (
                                                     PX XMemset []
                                                     (
                                                      PRun []
                                                      (
                                                       PX XMemset []
                                                       (
                                                        PRun []
                                                        (
                                                         PX XMemset []
                                                         (
                                                          PRun []
                                                          (
                                                           PX XMemset []
                                                           (
                                                            PRun []
                                                            (
                                                             PX XMemset []
                                                             (
                                                              PRun []
                                                              (
                                                               PX XMemset []
                                                               (
                                                                PRun []
                                                                (
                                                                 PX XMemset []
                                                                 (
                                                                  PRun []
                                                                  (
                                                                   PX XMemset []
                                                                   (
                                                                    PRun []
                                                                    (
                                                                     PX XMemset []
                                                                     (
                                                                      PRun []
                                                                      (
                                                                       PX XMemset []
                                                                       (
                                                                        PRun []
                                                                        (
                                                                         PX XMemset []
                                                                         (
                                                                          PRun []
                                                                          (
                                                                           PX XMemset []
                                                                           (
                                                                            PRun []
                                                                            (
                                                                             PX XMemset []
                                                                             (
                                                                              PRun []
                                                                              (
                                                                               PX XMemset []
                                                                               (
                                                                                PRun []
                                                                                (
                                                                                 PX XMemset []
                                                                                 (
                                                                                  PRun []
                                                                                  (
                                                                                   PX XMemset []
                                                                                   (
                                                                                    PRun []
                                                                                    (
                                                                                     PX XMemset []
                                                                                     (
                                                                                      PRun []
                                                                                      (
                                                                                       PX XMemset []
                                                                                       (
                                                                                        PRun []
                                                                                        (
                                                                                         PX XMemset []
                                                                                         (
                                                                                          PRun []
                                                                                          (
                                                                                           PX XMemset []
                                                                                           (
                                                                                            PRun []
                                                                                            (
                                                                                             PX XMemset []
                                                                                             (
                                                                                              PRun []
                                                                                              (
                                                                                               PX XMemset []
                                                                                               (
                                                                                                PRun []
                                                                                                (
                                                                                                 PX XMemset []
                                                                                                 (
                                                                                                  PRun []
                                                                                                  (
                                                                                                   PX XMemset []
                                                                                                   (
                                                                                                    PRun [0x96610]
                                                                                                    (
                                                                                                     PHandoff 3000   ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_via_U_slice : plan :=
  PRun []
  (
   PVia 3 js_3 183
   (
    PBrk2S
    (
     startup_plan_viafail6)
    (
     PRun []
     (
      PMmapIn
      (
       PSpin   )
      (
       PRun []
       (
        PBump 84
        (
         PIntroW 4295491576 [KRange (EVar 84) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 84)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6709248) (SA (escale 4096 (EVar 84)) 0) (ELit 8192)]
         (
          PGhost (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)
          (
           PMmap
           (
            PSpin   )
           (
            PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen
            (
             PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
             (
              PRun []
              (
               PX XIMemset []
               (
                PRun []
                (
                 PX XIMemset []
                 (
                  PBump 182
                  (
                   PFog 1 8192
                   (
                    PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (escale 4096 (EVar 5)) (ELit 8192)
                    (
                     PUnvis (escale 4096 (EVar 5)) (ELit 8192)
                     (
                      PHavocBrk 0x676000 0x80678000
                      (
                       PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
                       (
                        PMerge 3   ))))))))))))))))))
      (
       PSpin   ))))
   (
    PRename [(26, 22); (59, 23); (84, 24); (85, 25); (182, 26); (183, 27); (184, 28); (185, 29); (186, 30); (187, 31); (188, 32); (189, 33); (190, 34); (191, 35); (192, 36); (193, 37); (194, 38); (195, 39); (196, 40); (197, 41)]%nat
    (
     PCase2 (esub (eaddz (escale 16 (EVar 6)) 36703) (escale 4096 (EVar 22))) 4030
     (
      startup_plan_tail7)
     (
      startup_plan_tail8)))).

Definition startup_plan_hmset9 : plan :=
  PX XMemset []
  (
   PRun []
   (
    PX XMemset []
    (
     PRun []
     (
      PMmap
      (
       PSpin   )
      (
       PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) e_band e_bandlen
       (
        PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x666000)
        (
         PRun []
         (
          PX XMemcpy []
          (
           PRun []
           (
            PSys YBrk
            (
             startup_plan_via_U))))))))))).

Definition startup_plan_hmset10 : plan :=
  PX XMemset []
  (
   PDropRange (eaddz (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 26))) 2146398208) (eaddz (esub (escale 2 (EVar 6)) (escale 512 (EVar 26))) 4096)
   (
    PRun []
    (
     PX XMemset []
     (
      PRun []
      (
       PMmap
       (
        PSpin   )
       (
        PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) e_band e_bandlen
        (
         PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x666000)
         (
          PRun []
          (
           PX XMemcpy []
           (
            PRun []
            (
             PSys YBrk
             (
              startup_plan_via_U_slice)))))))))))).

Definition startup_plan_s2U11 : plan :=
  PRun [0x8292c]
  (
   PFresh 10 12 (Some (eaddz (escale 32768 (EVar 0)) (-32768)))
   (
    PRun []
    (
     PCase2 (esub (eaddz (escale 2 (EVar 6)) 11776) (escale 512 (EVar 26))) 7679
     (
      startup_plan_hmset9)
     (
      PVisSlice (eadd (escale 32768 (EVar 0)) (eaddz (escale 4096 (EVar 26)) (-8421376))) (esub e_band (eadd (escale 32768 (EVar 0)) (eaddz (escale 4096 (EVar 26)) (-8421376))))
      (
       startup_plan_hmset10))))).

Definition startup_plan : plan :=
  PRun []
  (
   PX XIMemset []
   (
    PRun []
    (
     PX XEnvScan []
     (
      PRun []
      (
       PX XPnScan []
       (
        PRun []
        (
         PX XIMemcpy []
         (
          PRun []
          (
           PSys YSetTid
           (
            PRun []
            (
             PRun [0xff378]
             (
              PHavocCell (ELit 0x673c70) 8
              (
               PRun [0x7b5d0]
               (
                PX XSniff []
                (
                 PRun []
                 (
                  PMmap
                  (
                   PSpin   )
                  (
                   PRun []
                   (
                    PMmap
                    (
                     PSpin   )
                    (
                     PRun []
                     (
                      PMmap
                      (
                       PSpin   )
                      (
                       PRun [0x7a3b4]
                       (
                        PX XIStrncpy []
                        (
                         PRun [0x7a3b4]
                         (
                          PX XIStrncpy []
                          (
                           PRun []
                           (
                            PMmap
                            (
                             PSpin   )
                            (
                             PShDisj (escale 4096 (EVar 77)) (ELit 0x10000) e_band e_bandlen
                             (
                              PShDisj (escale 4096 (EVar 77)) (ELit 0x10000) (ELit 0x10000) (ELit 0x666000)
                              (
                               PRun []
                               (
                                PX XIMemset []
                                (
                                 PRun []
                                 (
                                  PX XIMemcpy []
                                  (
                                   PRun []
                                   (
                                    PX XIMemcpy []
                                    (
                                     PRun [0x79bcc]
                                     (
                                      PRun [0x79bcc]
                                      (
                                       PRun [0x79bcc]
                                       (
                                        PRun [0x79bcc]
                                        (
                                         PRun [0x79bcc]
                                         (
                                          PRun [0x79bcc]
                                          (
                                           PRun [0x79bcc]
                                           (
                                            PRun [0x79bcc]
                                            (
                                             PRun [0x79bcc]
                                             (
                                              PRun [0x79bcc]
                                              (
                                               PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                               (
                                                PRun [0x79bcc]
                                                (
                                                 PRun [0x79bcc]
                                                 (
                                                  PRun [0x79bcc]
                                                  (
                                                   PRun [0x79bcc]
                                                   (
                                                    PRun [0x79bcc]
                                                    (
                                                     PRun [0x79bcc]
                                                     (
                                                      PRun [0x79bcc]
                                                      (
                                                       PRun [0x79bcc]
                                                       (
                                                        PRun [0x79bcc]
                                                        (
                                                         PRun [0x79bcc]
                                                         (
                                                          PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                          (
                                                           PRun [0x79bcc]
                                                           (
                                                            PRun [0x79bcc]
                                                            (
                                                             PRun [0x79bcc]
                                                             (
                                                              PRun [0x79bcc]
                                                              (
                                                               PRun [0x79bcc]
                                                               (
                                                                PRun [0x79bcc]
                                                                (
                                                                 PRun [0x79bcc]
                                                                 (
                                                                  PRun [0x79bcc]
                                                                  (
                                                                   PRun [0x79bcc]
                                                                   (
                                                                    PRun [0x79bcc]
                                                                    (
                                                                     PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                     (
                                                                      PRun [0x79bcc]
                                                                      (
                                                                       PRun [0x79bcc]
                                                                       (
                                                                        PRun [0x79bcc]
                                                                        (
                                                                         PRun [0x79bcc]
                                                                         (
                                                                          PRun [0x79bcc]
                                                                          (
                                                                           PRun [0x79bcc]
                                                                           (
                                                                            PRun [0x79bcc]
                                                                            (
                                                                             PRun [0x79bcc]
                                                                             (
                                                                              PRun [0x79bcc]
                                                                              (
                                                                               PRun [0x79bcc]
                                                                               (
                                                                                PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                (
                                                                                 PRun [0x79bcc]
                                                                                 (
                                                                                  PRun [0x79bcc]
                                                                                  (
                                                                                   PRun [0x79bcc]
                                                                                   (
                                                                                    PRun [0x79bcc]
                                                                                    (
                                                                                     PRun [0x79bcc]
                                                                                     (
                                                                                      PRun [0x79bcc]
                                                                                      (
                                                                                       PRun [0x79bcc]
                                                                                       (
                                                                                        PRun [0x79bcc]
                                                                                        (
                                                                                         PRun [0x79bcc]
                                                                                         (
                                                                                          PRun [0x79bcc]
                                                                                          (
                                                                                           PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                           (
                                                                                            PRun [0x79bcc]
                                                                                            (
                                                                                             PRun [0x79bcc]
                                                                                             (
                                                                                              PRun [0x79bcc]
                                                                                              (
                                                                                               PRun [0x79bcc]
                                                                                               (
                                                                                                PRun [0x79bcc]
                                                                                                (
                                                                                                 PRun [0x79bcc]
                                                                                                 (
                                                                                                  PRun [0x79bcc]
                                                                                                  (
                                                                                                   PRun [0x79bcc]
                                                                                                   (
                                                                                                    PRun [0x79bcc]
                                                                                                    (
                                                                                                     PRun [0x79bcc]
                                                                                                     (
                                                                                                      PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                      (
                                                                                                       PRun [0x79bcc]
                                                                                                       (
                                                                                                        PRun [0x79bcc]
                                                                                                        (
                                                                                                         PRun [0x79bcc]
                                                                                                         (
                                                                                                          PRun [0x79bcc]
                                                                                                          (
                                                                                                           PRun [0x79bcc]
                                                                                                           (
                                                                                                            PRun [0x79bcc]
                                                                                                            (
                                                                                                             PRun [0x79bcc]
                                                                                                             (
                                                                                                              PRun [0x79bcc]
                                                                                                              (
                                                                                                               PRun [0x79bcc]
                                                                                                               (
                                                                                                                PRun [0x79bcc]
                                                                                                                (
                                                                                                                 PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                 (
                                                                                                                  PRun [0x79bcc]
                                                                                                                  (
                                                                                                                   PRun [0x79bcc]
                                                                                                                   (
                                                                                                                    PRun [0x79bcc]
                                                                                                                    (
                                                                                                                     PRun [0x79bcc]
                                                                                                                     (
                                                                                                                      PRun [0x79bcc]
                                                                                                                      (
                                                                                                                       PRun [0x79bcc]
                                                                                                                       (
                                                                                                                        PRun [0x79bcc]
                                                                                                                        (
                                                                                                                         PRun [0x79bcc]
                                                                                                                         (
                                                                                                                          PRun [0x79bcc]
                                                                                                                          (
                                                                                                                           PRun [0x79bcc]
                                                                                                                           (
                                                                                                                            PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                            (
                                                                                                                             PRun [0x79bcc]
                                                                                                                             (
                                                                                                                              PRun [0x79bcc]
                                                                                                                              (
                                                                                                                               PRun [0x79bcc]
                                                                                                                               (
                                                                                                                                PRun [0x79bcc]
                                                                                                                                (
                                                                                                                                 PRun [0x79bcc]
                                                                                                                                 (
                                                                                                                                  PRun [0x79bcc]
                                                                                                                                  (
                                                                                                                                   PRun [0x79bcc]
                                                                                                                                   (
                                                                                                                                    PRun [0x79bcc]
                                                                                                                                    (
                                                                                                                                     PRun [0x79bcc]
                                                                                                                                     (
                                                                                                                                      PRun [0x79bcc]
                                                                                                                                      (
                                                                                                                                       PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                       (
                                                                                                                                        PRun [0x79bcc]
                                                                                                                                        (
                                                                                                                                         PRun [0x79bcc]
                                                                                                                                         (
                                                                                                                                          PRun [0x79bcc]
                                                                                                                                          (
                                                                                                                                           PRun [0x79bcc]
                                                                                                                                           (
                                                                                                                                            PRun [0x79bcc]
                                                                                                                                            (
                                                                                                                                             PRun [0x79bcc]
                                                                                                                                             (
                                                                                                                                              PRun [0x79bcc]
                                                                                                                                              (
                                                                                                                                               PRun [0x79bcc]
                                                                                                                                               (
                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                (
                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                 (
                                                                                                                                                  PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                  (
                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                   (
                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                    (
                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                     (
                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                      (
                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                       (
                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                        (
                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                         (
                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                          (
                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                           (
                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                            (
                                                                                                                                                             PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                             (
                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                              (
                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                               (
                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                (
                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                 (
                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                  (
                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                   (
                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                    (
                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                     (
                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                      (
                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                       (
                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                        (
                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                         (
                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                          (
                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                           (
                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                            (
                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                             (
                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                              (
                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                               (
                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                (
                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                 (
                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                  (
                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                   (
                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                    (
                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                     (
                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                      (
                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                       (
                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                        (
                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                         (
                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                          (
                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                           (
                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                            (
                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                             (
                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                              (
                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                               (
                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                (
                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                 (
                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                  (
                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                   (
                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                    (
                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                     (
                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                       (
                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                        (
                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                         (
                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                          (
                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                           (
                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                            (
                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                             (
                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                              (
                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                               (
                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                (
                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                 (
                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                  (
                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                   (
                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                    (
                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                     (
                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                       (
                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                        (
                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                         (
                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                          (
                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                           (
                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                            (
                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                              (
                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                          PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                     PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                           PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                      PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                 PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                            PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                       PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                  PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                             PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                    PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                               PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                         PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]
                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x79bcc]
                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                    PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                     PX XIMemcpy []
                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                      PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                       PX XIMemcpy []
                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                        PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                         PX XIMemset []
                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                          PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                           PX XIMemcpy []
                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                            PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                             PX XIMemcpy []
                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x6f9f0]
                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                               PDropRange (escale 4096 (EVar 77)) (ELit 0x10000)
                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x7b5d0]
                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                 PX XSniff []
                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                  PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                   PMmap
                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                    PSpin   )
                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                    PShDisj (escale 4096 (EVar 206)) (ELit 0x38e000) e_band e_bandlen
                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 206)) (ELit 0x38e000) (ELit 0x10000) (ELit 0x666000)
                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x66194]
                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                       PX XHeapSort []
                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                        PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                         PMmap
                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                          PSpin   )
                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                          PShDisj (escale 4096 (EVar 223)) (ELit 0x2000011000) e_band e_bandlen
                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                           PShDisj (escale 4096 (EVar 223)) (ELit 0x2000011000) (ELit 0x10000) (ELit 0x666000)
                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                            PDropRange (ELit 0x11e1b8) (ELit 0x12b0)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x823f8]
                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                              PFresh 9 12 None
                                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                                               PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                                PMmapIn
                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                 PSpin   )
                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                 PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                                  PX XMemset []
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                                   PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                                    PMmap
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                     PSpin   )
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 241)) (ELit 0x800000) e_band e_bandlen
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 241)) (ELit 0x800000) (ELit 0x10000) (ELit 0x666000)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                                       PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                                        PMmap
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PSpin   )
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PShDisj (escale 4096 (EVar 242)) (ELit 0x1000) e_band e_bandlen
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                                          PShDisj (escale 4096 (EVar 242)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                                           PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                                            PMmap
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PSpin   )
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PShDisj (escale 4096 (EVar 243)) (ELit 0x10000) e_band e_bandlen
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                              PShDisj (escale 4096 (EVar 243)) (ELit 0x10000) (ELit 0x10000) (ELit 0x666000)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                                                               PCaseDisjJ (ELit 0x7fff7000) (escale 4096 (EVar 243)) 0x698e4 []
                                                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                PBump 276
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                 PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  PX XMemset []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    PMmap
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PSpin   )
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 292)) (ELit 0x1000) e_band e_bandlen
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 292)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        PX XIMemcpy []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          PX XIMemcpy []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            PX XMemIsZero []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              PX XMemset []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                PMmap
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 PSpin   )
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 PShDisj (escale 4096 (EVar 357)) (ELit 0x1000) e_band e_bandlen
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  PShDisj (escale 4096 (EVar 357)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    PMmap
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PSpin   )
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 358)) (ELit 0x1000) e_band e_bandlen
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 358)) (ELit 0x1000) (ELit 0x10000) (ELit 0x666000)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        PX XIMemcpy []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          PX XIMemcpy []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           PRun []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            PSys YMunmap
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             PRename [(43, 10); (44, 11); (77, 12); (206, 13); (223, 14); (224, 15); (241, 16); (242, 17); (243, 18); (292, 19); (357, 20); (358, 21); (387, 22); (388, 23); (389, 24); (390, 25)]%nat
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              startup_plan_s2U11))))))))))))))))))))))))))))))))))))))))))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                 PSpin   ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_ranges : list (Z * nat) := [(0x44740, 320%nat); (0x46d40, 448%nat); (0x47f40, 128%nat); (0x4b540, 128%nat); (0x4bb40, 128%nat); (0x50840, 64%nat); (0x50f40, 128%nat); (0x51940, 1024%nat); (0x53040, 832%nat); (0x54440, 64%nat); (0x54b40, 896%nat); (0x56340, 192%nat); (0x5ae40, 64%nat); (0x5c540, 128%nat); (0x5d440, 6656%nat); (0x66140, 128%nat); (0x66740, 64%nat); (0x67140, 192%nat); (0x67940, 192%nat); (0x67f40, 256%nat); (0x68b40, 64%nat); (0x69540, 448%nat); (0x69f40, 192%nat); (0x6a940, 256%nat); (0x6ec40, 64%nat); (0x6f440, 64%nat); (0x6f940, 192%nat); (0x6fe40, 256%nat); (0x70440, 448%nat); (0x71540, 64%nat); (0x71840, 64%nat); (0x71e40, 1152%nat); (0x73f40, 192%nat); (0x74740, 192%nat); (0x75f40, 64%nat); (0x76640, 256%nat); (0x76d40, 64%nat); (0x77040, 192%nat); (0x77840, 128%nat); (0x77d40, 1216%nat); (0x79440, 832%nat); (0x7a340, 320%nat); (0x7aa40, 64%nat); (0x7b540, 128%nat); (0x7b940, 192%nat); (0x7be40, 128%nat); (0x7c340, 192%nat); (0x7ca40, 640%nat); (0x7d640, 192%nat); (0x7ee40, 384%nat); (0x7fa40, 768%nat); (0x80e40, 320%nat); (0x81a40, 192%nat); (0x82340, 64%nat); (0x82740, 640%nat); (0x83340, 64%nat); (0x83640, 192%nat); (0x83c40, 256%nat); (0x84540, 192%nat); (0x85f40, 128%nat); (0x86440, 192%nat); (0x86f40, 128%nat); (0x88740, 64%nat); (0x88a40, 256%nat); (0x89240, 256%nat); (0x89a40, 128%nat); (0x90540, 512%nat); (0x93340, 64%nat); (0x96340, 192%nat); (0x9b040, 128%nat); (0xfea40, 832%nat); (0xff934, 192%nat); (0x100234, 64%nat); (0x100934, 1088%nat); (0x104034, 128%nat); (0x10d934, 384%nat); (0x10e234, 320%nat); (0x10f634, 64%nat); (0x10fa34, 448%nat); (0x110634, 64%nat)]%Z.

