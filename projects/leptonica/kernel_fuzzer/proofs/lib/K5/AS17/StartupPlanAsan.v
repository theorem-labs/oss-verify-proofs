(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS17 Require Import StartupJSAsan.
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
       PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                 PHavocBrk 0x629000 0x8062b000  (* [comment removed for export] *)
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
      PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 84))  (* [comment removed for export] *)
       (
        startup_plan_wsplit1)
       (
        startup_plan_wsplit1)))))).

Definition startup_plan_tail3 : plan :=
  PRun [0x49d0c]  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                         (
                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                           (
                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                            (
                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                             (
                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                              (
                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                               (
                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                (
                                                                                                                                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                 (
                                                                                                                                                                                                  PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                  (
                                                                                                                                                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                   (
                                                                                                                                                                                                    PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                    (
                                                                                                                                                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                     (
                                                                                                                                                                                                      PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                       (
                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                        (
                                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                         (
                                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                          (
                                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                           (
                                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                            (
                                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                             (
                                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                              (
                                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                               (
                                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
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
                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 1613)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                       PShDisj (escale 4096 (EVar 1613)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                       (
                                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                        (
                                                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                         (
                                                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                          (
                                                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                           (
                                                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                            (
                                                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                              (
                                                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                  PRun [0x8c598]  (* [comment removed for export] *)
                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                   PHandoff 0  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail4 : plan :=
  PRun [0x49d0c]  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                         (
                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                           (
                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                            (
                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                             (
                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                              (
                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                               (
                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                (
                                                                                                                                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                 (
                                                                                                                                                                                                  PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                  (
                                                                                                                                                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                   (
                                                                                                                                                                                                    PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                    (
                                                                                                                                                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                     (
                                                                                                                                                                                                      PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                       (
                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                        (
                                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                         (
                                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                          (
                                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                           (
                                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                            (
                                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                             (
                                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                              (
                                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                               (
                                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
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
                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 1613)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                       PShDisj (escale 4096 (EVar 1613)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                       (
                                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                        (
                                                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                         (
                                                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                          (
                                                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                           (
                                                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                            (
                                                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                              (
                                                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                  PRun [0x8c598]  (* [comment removed for export] *)
                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                   PHandoff 1000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

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
         PIntroW 4295491576 [KRange (EVar 84) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 84)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6393856) (SA (escale 4096 (EVar 84)) 0) (ELit 8192)]  (* [comment removed for export] *)
         (
          PGhost (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)  (* [comment removed for export] *)
          (
           PMmap  (* [comment removed for export] *)
           (
            PSpin  (* [comment removed for export] *))
           (
            PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
            (
             PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                      PHavocBrk 0x629000 0x8062b000  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                 PHavocBrk 0x629000 0x8062b000  (* [comment removed for export] *)
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
      PShDisj (escale 4096 (EVar 84)) (ELit 0x2000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 84))  (* [comment removed for export] *)
       (
        startup_plan_wsplit5)
       (
        startup_plan_wsplit5)))))).

Definition startup_plan_tail7 : plan :=
  PRun [0x49d0c]  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                         (
                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                           (
                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                            (
                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                             (
                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                              (
                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                               (
                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                (
                                                                                                                                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                 (
                                                                                                                                                                                                  PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                  (
                                                                                                                                                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                   (
                                                                                                                                                                                                    PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                    (
                                                                                                                                                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                     (
                                                                                                                                                                                                      PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                       (
                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                        (
                                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                         (
                                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                          (
                                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                           (
                                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                            (
                                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                             (
                                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                              (
                                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                               (
                                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
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
                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 1613)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                       PShDisj (escale 4096 (EVar 1613)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                       (
                                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                        (
                                                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                         (
                                                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                          (
                                                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                           (
                                                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                            (
                                                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                              (
                                                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                  PRun [0x8c598]  (* [comment removed for export] *)
                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                   PHandoff 2000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail8 : plan :=
  PRun [0x49d0c]  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 42)) (ELit 0x100000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 43)) (ELit 0x800000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                 PShDisj (escale 4096 (EVar 60)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                         (
                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                           (
                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                            (
                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                             (
                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                              (
                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                               (
                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                (
                                                                                                                                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                 (
                                                                                                                                                                                                  PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                  (
                                                                                                                                                                                                   PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                   (
                                                                                                                                                                                                    PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                    (
                                                                                                                                                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                     (
                                                                                                                                                                                                      PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                       (
                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                        (
                                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                         (
                                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                          (
                                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                           (
                                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                            (
                                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                             (
                                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                              (
                                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                               (
                                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
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
                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 1613)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                       PShDisj (escale 4096 (EVar 1613)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                       (
                                                                                                                                                                                                                        PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                        (
                                                                                                                                                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                         (
                                                                                                                                                                                                                          PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                          (
                                                                                                                                                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                           (
                                                                                                                                                                                                                            PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                            (
                                                                                                                                                                                                                             PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                              PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                              (
                                                                                                                                                                                                                               PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                 PX XMemset []  (* [comment removed for export] *)
                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                  PRun [0x8c598]  (* [comment removed for export] *)
                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                   PHandoff 3000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

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
         PIntroW 4295491576 [KRange (EVar 84) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 84)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6393856) (SA (escale 4096 (EVar 84)) 0) (ELit 8192)]  (* [comment removed for export] *)
         (
          PGhost (eaddz (escale 4096 (EVar 84)) 4096) (ELit 4096)  (* [comment removed for export] *)
          (
           PMmap  (* [comment removed for export] *)
           (
            PSpin  (* [comment removed for export] *))
           (
            PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
            (
             PShDisj (escale 4096 (EVar 85)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                      PHavocBrk 0x629000 0x8062b000  (* [comment removed for export] *)
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
        PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
         PShDisj (escale 4096 (EVar 59)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
  PRun [0x788b4]  (* [comment removed for export] *)
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
             PRun [0xb65d4]  (* [comment removed for export] *)
             (
              PHavocCell (ELit 0x626bc8) 8  (* [comment removed for export] *)
              (
               PRun [0x71558]  (* [comment removed for export] *)
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
                       PRun [0x7033c]  (* [comment removed for export] *)
                       (
                        PX XIStrncpy []  (* [comment removed for export] *)
                        (
                         PRun [0x7033c]  (* [comment removed for export] *)
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
                              PShDisj (escale 4096 (EVar 77)) (ELit 0x10000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                     (
                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                      (
                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                       (
                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                        (
                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                         (
                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                          (
                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                           (
                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                            (
                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                             (
                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                              (
                                               PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                               (
                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                (
                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                 (
                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                  (
                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                   (
                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                    (
                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                     (
                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                      (
                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                       (
                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                        (
                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                         (
                                                          PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                          (
                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                           (
                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                            (
                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                             (
                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                              (
                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                               (
                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                (
                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                 (
                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                  (
                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                   (
                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                    (
                                                                     PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                     (
                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                      (
                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                       (
                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                        (
                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                         (
                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                          (
                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                           (
                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                            (
                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                             (
                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                              (
                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                               (
                                                                                PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                (
                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                 (
                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                  (
                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                    (
                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                     (
                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                      (
                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                        (
                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                          (
                                                                                           PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                            (
                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                             (
                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                              (
                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                               (
                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                (
                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                 (
                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                  (
                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                   (
                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                    (
                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                     (
                                                                                                      PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                      (
                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                       (
                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                        (
                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                         (
                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                          (
                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                           (
                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                            (
                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                             (
                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                              (
                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                               (
                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                (
                                                                                                                 PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                 (
                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                  (
                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                   (
                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                    (
                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                     (
                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                      (
                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                       (
                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                        (
                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                         (
                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                          (
                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                           (
                                                                                                                            PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                            (
                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                             (
                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                              (
                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                               (
                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                (
                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                 (
                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                  (
                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                   (
                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                    (
                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                     (
                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                      (
                                                                                                                                       PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                       (
                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                        (
                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                         (
                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                          (
                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                           (
                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                            (
                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                             (
                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                              (
                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                               (
                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                (
                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                 (
                                                                                                                                                  PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                  (
                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                   (
                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                    (
                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                     (
                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                      (
                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                       (
                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                        (
                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                         (
                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                          (
                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                           (
                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                            (
                                                                                                                                                             PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                             (
                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                              (
                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                               (
                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                (
                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                 (
                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                  (
                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                   (
                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                    (
                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                     (
                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                      (
                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                       (
                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                        (
                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                         (
                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                          (
                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                           (
                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                            (
                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                             (
                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                              (
                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                               (
                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                (
                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                 (
                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                  (
                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                   (
                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                    (
                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                     (
                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                      (
                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                       (
                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                        (
                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                         (
                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                           (
                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                            (
                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                             (
                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                              (
                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                               (
                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                (
                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                 (
                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                  (
                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                   (
                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                    (
                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                     (
                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                       (
                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                        (
                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                         (
                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                          (
                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                           (
                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                            (
                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                             (
                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                              (
                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                               (
                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                (
                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                 (
                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                  (
                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                   (
                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                    (
                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                     (
                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                       (
                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                        (
                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                         (
                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                          (
                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                           (
                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                            (
                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                              (
                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                          PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                     PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                           PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                      PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                 PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                            PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                       PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                  PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                             PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                    PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                               PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                         PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 77), ELit 1536); (eaddz (escale 4096 (EVar 77)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x6fb54]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x6fb54]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x65864]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                               PDropRange (escale 4096 (EVar 77)) (ELit 0x10000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x71558]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 206)) (ELit 0x38e000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x5c8ec]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                           PShDisj (escale 4096 (EVar 223)) (ELit 0x2000011000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                            PDropRange (ELit 0xd12b8) (ELit 0x12b0)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x78380]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 241)) (ELit 0x800000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                                       PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                                        PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PShDisj (escale 4096 (EVar 242)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                                          PShDisj (escale 4096 (EVar 242)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                                           PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                                            PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PShDisj (escale 4096 (EVar 243)) (ELit 0x10000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                              PShDisj (escale 4096 (EVar 243)) (ELit 0x10000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                                                               PCaseDisjJ (ELit 0x7fff7000) (escale 4096 (EVar 243)) 0x5fa48 []  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 292)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  PShDisj (escale 4096 (EVar 357)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 358)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 358)) (ELit 0x1000) (ELit 0x10000) (ELit 0x619000)  (* [comment removed for export] *)
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

Definition startup_plan_ranges : list (Z * nat) := [(0x3b300, 512%nat); (0x3db00, 512%nat); (0x3ed00, 192%nat); (0x42400, 128%nat); (0x42900, 192%nat); (0x47600, 192%nat); (0x47e00, 128%nat); (0x48400, 1088%nat); (0x49b00, 896%nat); (0x4af00, 128%nat); (0x4b600, 1024%nat); (0x4cf00, 192%nat); (0x51c00, 128%nat); (0x52c00, 192%nat); (0x53b00, 6720%nat); (0x5c800, 192%nat); (0x5d000, 256%nat); (0x5d800, 192%nat); (0x5de00, 320%nat); (0x5ec00, 128%nat); (0x5f700, 448%nat); (0x60000, 256%nat); (0x60800, 256%nat); (0x64a00, 128%nat); (0x65200, 128%nat); (0x65700, 640%nat); (0x66200, 512%nat); (0x67300, 128%nat); (0x67600, 192%nat); (0x67c00, 1216%nat); (0x69d00, 320%nat); (0x6a600, 256%nat); (0x6be00, 128%nat); (0x6c500, 128%nat); (0x6c800, 128%nat); (0x6cc00, 128%nat); (0x6cf00, 256%nat); (0x6d700, 256%nat); (0x6dc00, 1344%nat); (0x6f300, 1344%nat); (0x70900, 128%nat); (0x71400, 192%nat); (0x71800, 256%nat); (0x71d00, 256%nat); (0x72200, 320%nat); (0x72a00, 960%nat); (0x74d00, 512%nat); (0x75900, 832%nat); (0x76d00, 384%nat); (0x77900, 256%nat); (0x78200, 192%nat); (0x78600, 704%nat); (0x79300, 384%nat); (0x79b00, 320%nat); (0x7a400, 256%nat); (0x7be00, 192%nat); (0x7c300, 256%nat); (0x7ce00, 192%nat); (0x7e600, 128%nat); (0x7e900, 320%nat); (0x7f100, 320%nat); (0x7f900, 192%nat); (0x86400, 576%nat); (0x89200, 128%nat); (0x8c200, 256%nat); (0x8cc00, 128%nat); (0xb5c00, 896%nat); (0xb6c00, 192%nat); (0xb7400, 128%nat); (0xb7b00, 1152%nat); (0xbb000, 192%nat); (0xc0300, 192%nat); (0xc0700, 192%nat); (0xc0c00, 384%nat); (0xc1f00, 192%nat); (0xc2300, 192%nat); (0xc2700, 256%nat); (0xc2f00, 128%nat)]%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
