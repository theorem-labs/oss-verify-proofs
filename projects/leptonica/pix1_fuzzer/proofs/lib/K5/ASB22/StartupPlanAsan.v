(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.ASB22 Require Import StartupJSAsan.
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
      PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PX XIMemset []  (* [comment removed for export] *)
         (
          PRun []  (* [comment removed for export] *)
          (
           PX XIMemset []  (* [comment removed for export] *)
           (
            PBump 182  (* [comment removed for export] *)
            (
             PFog 1 8192  (* [comment removed for export] *)
             (
              PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)  (* [comment removed for export] *)
              (
               PUnvis (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)  (* [comment removed for export] *)
               (
                PGhost (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                (
                 PHavocBrk 0x628000 0x8062a000  (* [comment removed for export] *)
                 (
                  PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat  (* [comment removed for export] *)
                  (
                   PMerge 0  (* [comment removed for export] *)))))))))))))))))).

Definition startup_plan_viafail2 : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PBump 84  (* [comment removed for export] *)
   (
    PMmap  (* [comment removed for export] *)
    (
     PSpin  (* [comment removed for export] *))
    (
     PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) e_band e_bandlen  (* [comment removed for export] *)
     (
      PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 84))  (* [comment removed for export] *)
       (
        startup_plan_wsplit1)
       (
        startup_plan_wsplit1)))))).

Definition startup_plan_tail3 : plan :=
  PRun [0x49700]  (* [comment removed for export] *)
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                (
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                          PShDisj (escale 4096 (EVar 1389)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PShDisj (escale 4096 (EVar 1389)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                                      PRun [0x8bf8c]  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PHandoff 0  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail4 : plan :=
  PRun [0x49700]  (* [comment removed for export] *)
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                (
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                          PShDisj (escale 4096 (EVar 1389)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PShDisj (escale 4096 (EVar 1389)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                                      PRun [0x8bf8c]  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PHandoff 1000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_via_U : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PVia 0 js_0 183  (* [comment removed for export] *)
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
        PBump 84  (* [comment removed for export] *)
        (
         PIntroW 4295491576 [KRange (EVar 84) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 84)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6389760) (SA (escale 4096 (EVar 84)) 0) (ELit 8192)]  (* [comment removed for export] *)
         (
          PGhost (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)  (* [comment removed for export] *)
          (
           PMmap  (* [comment removed for export] *)
           (
            PSpin  (* [comment removed for export] *))
           (
            PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
            (
             PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
             (
              PRun []  (* [comment removed for export] *)
              (
               PX XIMemset []  (* [comment removed for export] *)
               (
                PRun []  (* [comment removed for export] *)
                (
                 PX XIMemset []  (* [comment removed for export] *)
                 (
                  PBump 182  (* [comment removed for export] *)
                  (
                   PFog 1 8192  (* [comment removed for export] *)
                   (
                    PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                    (
                     PUnvis (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                     (
                      PHavocBrk 0x628000 0x8062a000  (* [comment removed for export] *)
                      (
                       PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat  (* [comment removed for export] *)
                       (
                        PMerge 0  (* [comment removed for export] *)))))))))))))))))))
      (
       PSpin  (* [comment removed for export] *)))))
   (
    PRename [(26, 22); (59, 23); (84, 24); (85, 25); (182, 26); (183, 27); (184, 28); (185, 29); (186, 30); (187, 31); (188, 32); (189, 33); (190, 34); (191, 35); (192, 36); (193, 37); (194, 38); (195, 39); (196, 40); (197, 41)]%nat  (* [comment removed for export] *)
    (
     PCase2 (esub (eaddz (escale 16 (EVar 6)) 36703) (escale 4096 (EVar 22))) 4030  (* [comment removed for export] *)
     (
      startup_plan_tail3)
     (
      startup_plan_tail4)))).

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
      PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PX XIMemset []  (* [comment removed for export] *)
         (
          PRun []  (* [comment removed for export] *)
          (
           PX XIMemset []  (* [comment removed for export] *)
           (
            PBump 182  (* [comment removed for export] *)
            (
             PFog 1 8192  (* [comment removed for export] *)
             (
              PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)  (* [comment removed for export] *)
              (
               PUnvis (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)  (* [comment removed for export] *)
               (
                PGhost (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                (
                 PHavocBrk 0x628000 0x8062a000  (* [comment removed for export] *)
                 (
                  PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat  (* [comment removed for export] *)
                  (
                   PMerge 3  (* [comment removed for export] *)))))))))))))))))).

Definition startup_plan_viafail6 : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PBump 84  (* [comment removed for export] *)
   (
    PMmap  (* [comment removed for export] *)
    (
     PSpin  (* [comment removed for export] *))
    (
     PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) e_band e_bandlen  (* [comment removed for export] *)
     (
      PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 84))  (* [comment removed for export] *)
       (
        startup_plan_wsplit5)
       (
        startup_plan_wsplit5)))))).

Definition startup_plan_tail7 : plan :=
  PRun [0x49700]  (* [comment removed for export] *)
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                (
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                          PShDisj (escale 4096 (EVar 1389)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PShDisj (escale 4096 (EVar 1389)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                                      PRun [0x8bf8c]  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PHandoff 2000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail8 : plan :=
  PRun [0x49700]  (* [comment removed for export] *)
  (
   PJoin (eadd (escale 32768 (EVar 0)) (escale 16 (EVar 6))) (-2280) 8  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PMmap  (* [comment removed for export] *)
     (
      PSpin  (* [comment removed for export] *))
     (
      PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) e_band e_bandlen  (* [comment removed for export] *)
      (
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                (
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                          PShDisj (escale 4096 (EVar 1389)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PShDisj (escale 4096 (EVar 1389)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                                      PRun [0x8bf8c]  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PHandoff 3000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_via_U_slice : plan :=
  PRun []  (* [comment removed for export] *)
  (
   PVia 3 js_3 183  (* [comment removed for export] *)
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
        PBump 84  (* [comment removed for export] *)
        (
         PIntroW 4295491576 [KRange (EVar 84) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 84)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6389760) (SA (escale 4096 (EVar 84)) 0) (ELit 8192)]  (* [comment removed for export] *)
         (
          PGhost (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)  (* [comment removed for export] *)
          (
           PMmap  (* [comment removed for export] *)
           (
            PSpin  (* [comment removed for export] *))
           (
            PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
            (
             PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
             (
              PRun []  (* [comment removed for export] *)
              (
               PX XIMemset []  (* [comment removed for export] *)
               (
                PRun []  (* [comment removed for export] *)
                (
                 PX XIMemset []  (* [comment removed for export] *)
                 (
                  PBump 182  (* [comment removed for export] *)
                  (
                   PFog 1 8192  (* [comment removed for export] *)
                   (
                    PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                    (
                     PUnvis (escale 4096 (EVar 5)) (ELit 8192)  (* [comment removed for export] *)
                     (
                      PHavocBrk 0x628000 0x8062a000  (* [comment removed for export] *)
                      (
                       PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat  (* [comment removed for export] *)
                       (
                        PMerge 3  (* [comment removed for export] *)))))))))))))))))))
      (
       PSpin  (* [comment removed for export] *)))))
   (
    PRename [(26, 22); (59, 23); (84, 24); (85, 25); (182, 26); (183, 27); (184, 28); (185, 29); (186, 30); (187, 31); (188, 32); (189, 33); (190, 34); (191, 35); (192, 36); (193, 37); (194, 38); (195, 39); (196, 40); (197, 41)]%nat  (* [comment removed for export] *)
    (
     PCase2 (esub (eaddz (escale 16 (EVar 6)) 36703) (escale 4096 (EVar 22))) 4030  (* [comment removed for export] *)
     (
      startup_plan_tail7)
     (
      startup_plan_tail8)))).

Definition startup_plan_hmset9 : plan :=
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
       PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) e_band e_bandlen  (* [comment removed for export] *)
       (
        PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
        (
         PRun []  (* [comment removed for export] *)
         (
          PX XMemcpy []  (* [comment removed for export] *)
          (
           PRun []  (* [comment removed for export] *)
           (
            PSys YBrk  (* [comment removed for export] *)
            (
             startup_plan_via_U))))))))))).

Definition startup_plan_hmset10 : plan :=
  PX XMemset []  (* [comment removed for export] *)
  (
   PDropRange (eaddz (eadd (escale 4096 (EVar 0)) (escale 512 (EVar 26))) 2146398208) (eaddz (esub (escale 2 (EVar 6)) (escale 512 (EVar 26))) 4096)  (* [comment removed for export] *)
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
        PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) e_band e_bandlen  (* [comment removed for export] *)
        (
         PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
         (
          PRun []  (* [comment removed for export] *)
          (
           PX XMemcpy []  (* [comment removed for export] *)
           (
            PRun []  (* [comment removed for export] *)
            (
             PSys YBrk  (* [comment removed for export] *)
             (
              startup_plan_via_U_slice)))))))))))).

Definition startup_plan_s2U11 : plan :=
  PRun [0x782a8]  (* [comment removed for export] *)
  (
   PFresh 10 12 (Some (eaddz (escale 32768 (EVar 0)) (-32768)))  (* [comment removed for export] *)
   (
    PRun []  (* [comment removed for export] *)
    (
     PCase2 (esub (eaddz (escale 2 (EVar 6)) 11776) (escale 512 (EVar 26))) 7679  (* [comment removed for export] *)
     (
      startup_plan_hmset9)
     (
      PVisSlice (eadd (escale 32768 (EVar 0)) (eaddz (escale 4096 (EVar 26)) (-8421376))) (esub e_band (eadd (escale 32768 (EVar 0)) (eaddz (escale 4096 (EVar 26)) (-8421376))))  (* [comment removed for export] *)
      (
       startup_plan_hmset10))))).

Definition startup_plan : plan :=
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
             PRun [0xb56ec]  (* [comment removed for export] *)
             (
              PHavocCell (ELit 0x625948) 8  (* [comment removed for export] *)
              (
               PRun [0x70f4c]  (* [comment removed for export] *)
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
                       PRun [0x6fd30]  (* [comment removed for export] *)
                       (
                        PX XIStrncpy []  (* [comment removed for export] *)
                        (
                         PRun [0x6fd30]  (* [comment removed for export] *)
                         (
                          PX XIStrncpy []  (* [comment removed for export] *)
                          (
                           PRun []  (* [comment removed for export] *)
                           (
                            PMmap  (* [comment removed for export] *)
                            (
                             PSpin  (* [comment removed for export] *))
                            (
                             PShDisj (escale 4096 (EVar 77)) (ELit 0x10000) e_band e_bandlen  (* [comment removed for export] *)
                             (
                              PShDisj (escale 4096 (EVar 77)) (ELit 0x10000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                     PRun [0x6f548]  (* [comment removed for export] *)
                                     (
                                      PRun [0x6f548]  (* [comment removed for export] *)
                                      (
                                       PRun [0x6f548]  (* [comment removed for export] *)
                                       (
                                        PRun [0x6f548]  (* [comment removed for export] *)
                                        (
                                         PRun [0x6f548]  (* [comment removed for export] *)
                                         (
                                          PRun [0x6f548]  (* [comment removed for export] *)
                                          (
                                           PRun [0x6f548]  (* [comment removed for export] *)
                                           (
                                            PRun [0x6f548]  (* [comment removed for export] *)
                                            (
                                             PRun [0x6f548]  (* [comment removed for export] *)
                                             (
                                              PRun [0x6f548]  (* [comment removed for export] *)
                                              (
                                               PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                               (
                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                (
                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                 (
                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                  (
                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                   (
                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                    (
                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                     (
                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                      (
                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                       (
                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                        (
                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                         (
                                                          PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                          (
                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                           (
                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                            (
                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                             (
                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                              (
                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                               (
                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                (
                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                 (
                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                  (
                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                   (
                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                    (
                                                                     PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                     (
                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                      (
                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                       (
                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                        (
                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                         (
                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                          (
                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                           (
                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                            (
                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                             (
                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                              (
                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                               (
                                                                                PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                (
                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                 (
                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                  (
                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                    (
                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                     (
                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                      (
                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                        (
                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                          (
                                                                                           PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                            (
                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                             (
                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                              (
                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                               (
                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                (
                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                 (
                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                  (
                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                   (
                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                    (
                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                     (
                                                                                                      PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                      (
                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                       (
                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                        (
                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                         (
                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                          (
                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                           (
                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                            (
                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                             (
                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                              (
                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                               (
                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                (
                                                                                                                 PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                 (
                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                  (
                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                   (
                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                    (
                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                     (
                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                      (
                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                       (
                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                        (
                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                         (
                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                          (
                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                           (
                                                                                                                            PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                            (
                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                             (
                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                              (
                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                               (
                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                (
                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                 (
                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                  (
                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                   (
                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                    (
                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                     (
                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                      (
                                                                                                                                       PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                       (
                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                        (
                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                         (
                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                          (
                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                           (
                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                            (
                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                             (
                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                              (
                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                               (
                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                (
                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                 (
                                                                                                                                                  PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                  (
                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                   (
                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                    (
                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                     (
                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                      (
                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                       (
                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                        (
                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                         (
                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                          (
                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                           (
                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                            (
                                                                                                                                                             PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                             (
                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                              (
                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                               (
                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                (
                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                 (
                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                  (
                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                   (
                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                    (
                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                     (
                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                      (
                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                       (
                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                        (
                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                         (
                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                          (
                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                           (
                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                            (
                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                             (
                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                              (
                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                               (
                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                (
                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                 (
                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                  (
                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                   (
                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                    (
                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                     (
                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                      (
                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                       (
                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                        (
                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                         (
                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                           (
                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                            (
                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                             (
                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                              (
                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                               (
                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                (
                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                 (
                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                  (
                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                   (
                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                    (
                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                     (
                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                       (
                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                        (
                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                         (
                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                          (
                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                           (
                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                            (
                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                             (
                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                              (
                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                               (
                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                (
                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                 (
                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                  (
                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                   (
                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                    (
                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                     (
                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                       (
                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                        (
                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                         (
                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                          (
                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                           (
                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                            (
                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                              (
                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                          PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                     PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                           PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                      PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                 PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                            PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                       PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                  PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                             PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                    PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                               PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                         PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x6f548]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x6f548]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x65258]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                               PDropRange (escale 4096 (EVar 77)) (ELit 0x10000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x70f4c]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                 PX XSniff []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                  PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                   PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                    PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                    PShDisj (escale 4096 (EVar 206)) (ELit 0x38e000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 206)) (ELit 0x38e000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x5c2e0]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                       PX XHeapSort []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                         PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                          PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                          PShDisj (escale 4096 (EVar 223)) (ELit 0x2000011000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                           PShDisj (escale 4096 (EVar 223)) (ELit 0x2000011000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                            PDropRange (ELit 0xd0038) (ELit 0x12b0)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x77d74]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 241)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 241)) (ELit 0x800000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                                       PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                                        PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PShDisj (escale 4096 (EVar 242)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                                          PShDisj (escale 4096 (EVar 242)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                                           PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                                            PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PShDisj (escale 4096 (EVar 243)) (ELit 0x10000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                              PShDisj (escale 4096 (EVar 243)) (ELit 0x10000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                                                               PCaseDisjJ (ELit 0x7fff7000) (escale 4096 (EVar 243)) 0x5f43c []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                PBump 276  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 292)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 292)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 PShDisj (escale 4096 (EVar 357)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  PShDisj (escale 4096 (EVar 357)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 358)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 358)) (ELit 0x1000) (ELit 0x10000) (ELit 0x618000)  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             PRename [(43, 10); (44, 11); (77, 12); (206, 13); (223, 14); (224, 15); (241, 16); (242, 17); (243, 18); (292, 19); (357, 20); (358, 21); (387, 22); (388, 23); (389, 24); (390, 25)]%nat  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              startup_plan_s2U11))))))))))))))))))))))))))))))))))))))))))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                                                 PSpin  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_ranges : list (Z * nat) := [(0x3ae00, 384%nat); (0x3d400, 512%nat); (0x3e600, 192%nat); (0x41d00, 192%nat); (0x42300, 192%nat); (0x46f00, 192%nat); (0x47700, 128%nat); (0x47d00, 1088%nat); (0x49400, 960%nat); (0x4a800, 192%nat); (0x4b000, 256%nat); (0x4b500, 640%nat); (0x4c800, 192%nat); (0x51600, 128%nat); (0x52600, 256%nat); (0x53500, 6784%nat); (0x5c200, 192%nat); (0x5ca00, 256%nat); (0x5d200, 256%nat); (0x5d800, 320%nat); (0x5e600, 128%nat); (0x5f100, 448%nat); (0x5fa00, 256%nat); (0x60200, 256%nat); (0x64500, 128%nat); (0x64c00, 192%nat); (0x65100, 640%nat); (0x65c00, 576%nat); (0x66d00, 384%nat); (0x67600, 320%nat); (0x67c00, 832%nat); (0x69800, 256%nat); (0x6a000, 256%nat); (0x6b800, 192%nat); (0x6bf00, 128%nat); (0x6c200, 128%nat); (0x6c600, 128%nat); (0x6c900, 256%nat); (0x6d100, 256%nat); (0x6d600, 1344%nat); (0x6ee00, 576%nat); (0x6f800, 640%nat); (0x70300, 128%nat); (0x70e00, 192%nat); (0x71200, 576%nat); (0x71c00, 320%nat); (0x72400, 960%nat); (0x74800, 448%nat); (0x75300, 832%nat); (0x76700, 384%nat); (0x77300, 256%nat); (0x77c00, 192%nat); (0x78100, 640%nat); (0x78d00, 128%nat); (0x79000, 192%nat); (0x79500, 384%nat); (0x79f00, 256%nat); (0x7b900, 128%nat); (0x7bd00, 256%nat); (0x7c800, 192%nat); (0x7e000, 512%nat); (0x7eb00, 320%nat); (0x7f300, 192%nat); (0x85e00, 384%nat); (0x86500, 128%nat); (0x88c00, 128%nat); (0x8bc00, 256%nat); (0x8c500, 192%nat); (0xb4d00, 896%nat); (0xb5d00, 256%nat); (0xb6600, 128%nat); (0xb6c00, 1216%nat); (0xba100, 192%nat); (0xbf400, 448%nat); (0xbfd00, 384%nat); (0xc1100, 128%nat); (0xc1400, 192%nat); (0xc1800, 256%nat); (0xc2100, 128%nat)]%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
