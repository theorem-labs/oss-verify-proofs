(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up plan's fresh-variable indices and the CONFIG_RSEQ flag of its snapshots). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import StartupJSBoth.
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
       PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                 PHavocBrk 0x62b000 0x8062d000  (* [comment removed for export] *)
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
      PShDisj (escale 4096 (EVar 86)) (ELit 0x2000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 86))  (* [comment removed for export] *)
       (
        startup_plan_wsplit1)
       (
        startup_plan_wsplit1)))))).

Definition startup_plan_tail3 : plan :=
  PRun [0x3fea4]  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                 PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                                                                                 PMmap  (* [comment removed for export] *)
                                                                                 (
                                                                                  PSpin  (* [comment removed for export] *))
                                                                                 (
                                                                                  PShDisj (escale 4096 (EVar 559)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                  (
                                                                                   PShDisj (escale 4096 (EVar 559)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun []  (* [comment removed for export] *)
                                                                                    (
                                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                                     (
                                                                                      PRun []  (* [comment removed for export] *)
                                                                                      (
                                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun []  (* [comment removed for export] *)
                                                                                        (
                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun []  (* [comment removed for export] *)
                                                                                          (
                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun [0x80e64]  (* [comment removed for export] *)
                                                                                            (
                                                                                             PHandoff 0  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail4 : plan :=
  PRun [0x3fea4]  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                 PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                                                                                 PMmap  (* [comment removed for export] *)
                                                                                 (
                                                                                  PSpin  (* [comment removed for export] *))
                                                                                 (
                                                                                  PShDisj (escale 4096 (EVar 559)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                  (
                                                                                   PShDisj (escale 4096 (EVar 559)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun []  (* [comment removed for export] *)
                                                                                    (
                                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                                     (
                                                                                      PRun []  (* [comment removed for export] *)
                                                                                      (
                                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun []  (* [comment removed for export] *)
                                                                                        (
                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun []  (* [comment removed for export] *)
                                                                                          (
                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun [0x80e64]  (* [comment removed for export] *)
                                                                                            (
                                                                                             PHandoff 1000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* CW44B: the recorded join snapshots [js_0] / [js_3] now
   take the run's CONFIG_RSEQ flag, because nine of their stack-geometry rows differ
   between the two arms by exactly one numeral (#38's auxv gains the two AT_RSEQ pairs,
   32 bytes).  The four definitions between here and [startup_plan] carry the flag for
   no other reason; no node's text changes.  See StartupJSBoth.v's header. *)
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
         PIntroW 4295491576 [KRange (EVar 86) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 86)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6402048) (SA (escale 4096 (EVar 86)) 0) (ELit 8192)]  (* [comment removed for export] *)
         (
          PGhost (eaddz (escale 4096 (EVar 86)) 4096) (ELit 4096)  (* [comment removed for export] *)
          (
           PMmap  (* [comment removed for export] *)
           (
            PSpin  (* [comment removed for export] *))
           (
            PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
            (
             PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                      PHavocBrk 0x62b000 0x8062d000  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                 PHavocBrk 0x62b000 0x8062d000  (* [comment removed for export] *)
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
      PShDisj (escale 4096 (EVar 86)) (ELit 0x2000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
      (
       PCaseDisj (ELit 0x7fff7000) (escale 4096 (EVar 86))  (* [comment removed for export] *)
       (
        startup_plan_wsplit5)
       (
        startup_plan_wsplit5)))))).

Definition startup_plan_tail7 : plan :=
  PRun [0x3fea4]  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                 PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                                                                                 PMmap  (* [comment removed for export] *)
                                                                                 (
                                                                                  PSpin  (* [comment removed for export] *))
                                                                                 (
                                                                                  PShDisj (escale 4096 (EVar 559)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                  (
                                                                                   PShDisj (escale 4096 (EVar 559)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun []  (* [comment removed for export] *)
                                                                                    (
                                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                                     (
                                                                                      PRun []  (* [comment removed for export] *)
                                                                                      (
                                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun []  (* [comment removed for export] *)
                                                                                        (
                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun []  (* [comment removed for export] *)
                                                                                          (
                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun [0x80e64]  (* [comment removed for export] *)
                                                                                            (
                                                                                             PHandoff 2000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_tail8 : plan :=
  PRun [0x3fea4]  (* [comment removed for export] *)
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
       PShDisj (escale 4096 (EVar 44)) (ELit 0x100000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
       (
        PRun []  (* [comment removed for export] *)
        (
         PMmap  (* [comment removed for export] *)
         (
          PSpin  (* [comment removed for export] *))
         (
          PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) e_band e_bandlen  (* [comment removed for export] *)
          (
           PShDisj (escale 4096 (EVar 45)) (ELit 0x800000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                 PShDisj (escale 4096 (EVar 62)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                                                                                 PMmap  (* [comment removed for export] *)
                                                                                 (
                                                                                  PSpin  (* [comment removed for export] *))
                                                                                 (
                                                                                  PShDisj (escale 4096 (EVar 559)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                  (
                                                                                   PShDisj (escale 4096 (EVar 559)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun []  (* [comment removed for export] *)
                                                                                    (
                                                                                     PX XMemset []  (* [comment removed for export] *)
                                                                                     (
                                                                                      PRun []  (* [comment removed for export] *)
                                                                                      (
                                                                                       PX XMemset []  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun []  (* [comment removed for export] *)
                                                                                        (
                                                                                         PX XMemset []  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun []  (* [comment removed for export] *)
                                                                                          (
                                                                                           PX XMemset []  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun [0x80e64]  (* [comment removed for export] *)
                                                                                            (
                                                                                             PHandoff 3000  (* [comment removed for export] *)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_via_U_slice (r : Z) : plan :=
  PRun []  (* [comment removed for export] *)
  (
   (* LPS 75d69e00 (#38).  The twin of [StartupPlanAsan.v]'s change; read that file's
      comment for the measurement.  Same omission, same cause, same map: this slice
      joins [js_3], which is [js_0] but for [a_abytes], so it needs the same variable
      correspondence [startup_plan_via_U] carries at line 466, and the walk refused
      here with the identical via_ok mask 23 and nxt cs 445 once the
      [startup_plan_hmset10] arm was opened. *)
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
         PIntroW 4295491576 [KRange (EVar 86) 1 34359736318; KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (escale 4096 (EVar 86)) 0) (ELit 8192); KDisj (SA (ELit 65536) 0) (ELit 6402048) (SA (escale 4096 (EVar 86)) 0) (ELit 8192)]  (* [comment removed for export] *)
         (
          PGhost (eaddz (escale 4096 (EVar 86)) 4096) (ELit 4096)  (* [comment removed for export] *)
          (
           PMmap  (* [comment removed for export] *)
           (
            PSpin  (* [comment removed for export] *))
           (
            PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
            (
             PShDisj (escale 4096 (EVar 87)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                      PHavocBrk 0x62b000 0x8062d000  (* [comment removed for export] *)
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
        PShDisj (escale 4096 (EVar 428)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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

(* LPS 75d69e00 (#38).  The twin of [StartupPlanAsan.v]'s [startup_plan_hmset10];
   read that file's comment for the measurement.  Here too this is the else arm of
   the [PCase2] in [startup_plan_s2U11] below, [startup_plan_hmset9] is the then
   arm, both arms [PMmap] the same 0xb09000 region at the same point of the walk,
   and the then arm already names [EVar 428].  The farm printed the same refusal
   for this tree at pc 413668, best 428, named 61. *)
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
         PShDisj (escale 4096 (EVar 428)) (ELit 0xb09000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
  PRun [0x6d180]  (* [comment removed for export] *)
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

(* LPS 75d69e00 (#38): see StartupPlanAsan.v.  Indexed by the run's CONFIG_RSEQ
   flag, as [K/A/TopA.v:63] and [K/A/TopA_start.v:79] already state; the plan text
   is unchanged because at this revision the flag reaches the walk through
   [check]'s own [rz] argument, not through the plan's nodes. *)
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
             PRun [0xbc400]  (* [comment removed for export] *)
             (
              PHavocCell (ELit 0x629518) 8  (* [comment removed for export] *)
              (
               PRun [0x65e24]  (* [comment removed for export] *)
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
                       PRun [0x64c08]  (* [comment removed for export] *)
                       (
                        PX XIStrncpy []  (* [comment removed for export] *)
                        (
                         PRun [0x64c08]  (* [comment removed for export] *)
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
                              PShDisj (escale 4096 (EVar 81)) (ELit 0x10000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                                     PRun [0x64420]  (* [comment removed for export] *)
                                     (
                                      PRun [0x64420]  (* [comment removed for export] *)
                                      (
                                       PRun [0x64420]  (* [comment removed for export] *)
                                       (
                                        PRun [0x64420]  (* [comment removed for export] *)
                                        (
                                         PRun [0x64420]  (* [comment removed for export] *)
                                         (
                                          PRun [0x64420]  (* [comment removed for export] *)
                                          (
                                           PRun [0x64420]  (* [comment removed for export] *)
                                           (
                                            PRun [0x64420]  (* [comment removed for export] *)
                                            (
                                             PRun [0x64420]  (* [comment removed for export] *)
                                             (
                                              PRun [0x64420]  (* [comment removed for export] *)
                                              (
                                               PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                               (
                                                PRun [0x64420]  (* [comment removed for export] *)
                                                (
                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                 (
                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                  (
                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                   (
                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                    (
                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                     (
                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                      (
                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                       (
                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                        (
                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                         (
                                                          PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                          (
                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                           (
                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                            (
                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                             (
                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                              (
                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                               (
                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                (
                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                 (
                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                  (
                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                   (
                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                    (
                                                                     PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                     (
                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                      (
                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                       (
                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                        (
                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                         (
                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                          (
                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                           (
                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                            (
                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                             (
                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                              (
                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                               (
                                                                                PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                (
                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                 (
                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                  (
                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                   (
                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                    (
                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                     (
                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                      (
                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                       (
                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                        (
                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                         (
                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                          (
                                                                                           PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                           (
                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                            (
                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                             (
                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                              (
                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                               (
                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                (
                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                 (
                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                  (
                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                   (
                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                    (
                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                     (
                                                                                                      PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                      (
                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                       (
                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                        (
                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                         (
                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                          (
                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                           (
                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                            (
                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                             (
                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                              (
                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                               (
                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                (
                                                                                                                 PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                 (
                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                  (
                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                   (
                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                    (
                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                     (
                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                      (
                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                       (
                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                        (
                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                         (
                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                          (
                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                           (
                                                                                                                            PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                            (
                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                             (
                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                              (
                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                               (
                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                (
                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                 (
                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                  (
                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                   (
                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                    (
                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                     (
                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                      (
                                                                                                                                       PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                       (
                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                        (
                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                         (
                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                          (
                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                           (
                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                            (
                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                             (
                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                              (
                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                               (
                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                (
                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                 (
                                                                                                                                                  PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                  (
                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                   (
                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                    (
                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                     (
                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                      (
                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                       (
                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                        (
                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                         (
                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                          (
                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                           (
                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                            (
                                                                                                                                                             PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                             (
                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                              (
                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                               (
                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                (
                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                 (
                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                  (
                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                   (
                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                    (
                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                     (
                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                      (
                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                       (
                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                        (
                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                         (
                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                          (
                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                           (
                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                            (
                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                             (
                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                              (
                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                               (
                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                (
                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                 (
                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                  (
                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                   (
                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                    (
                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                     (
                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                      (
                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                       (
                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                        (
                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                         (
                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                          (
                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                           (
                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                            (
                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                             (
                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                              (
                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                               (
                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                (
                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                 (
                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                  (
                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                   (
                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                    (
                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                     (
                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                      (
                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                       (
                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                        (
                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                         (
                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                          (
                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                           (
                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                            (
                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                             (
                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                              (
                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                               (
                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                (
                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                 (
                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                  (
                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                   (
                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                    (
                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                     (
                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                      (
                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                       (
                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                        (
                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                         (
                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                          (
                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                           (
                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                            (
                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                             (
                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                              (
                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                          PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                     PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                           PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                      PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                 PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                            PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                       PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                  PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                             PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                        PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                   PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                              PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                    PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                         PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                               PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                    PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                     PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                       PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                        PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                         PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                          PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                           PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                            PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                               PGcKeep [(escale 4096 (EVar 79), ELit 1536); (eaddz (escale 4096 (EVar 79)) 5808, ELit 16)]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                (
                                                                                                                                                                                                                                                                                                                                                                                                                 PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                 (
                                                                                                                                                                                                                                                                                                                                                                                                                  PRun [0x64420]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                   PRun [0x64420]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                              PRun [0x5a244]  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                               PDropRange (escale 4096 (EVar 81)) (ELit 0x10000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                               (
                                                                                                                                                                                                                                                                                                                                                                                                                                PRun [0x65e24]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 210)) (ELit 0x38e000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                      PRun [0x52788]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                           PShDisj (escale 4096 (EVar 227)) (ELit 0x2000011000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                            PDropRange (ELit 0xd3e38) (ELit 0x12b0)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                             PRun [0x6cc4c]  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 245)) (ELit 0x800000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (
                                                                                                                                                                                                                                                                                                                                                                                                                                                       PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (
                                                                                                                                                                                                                                                                                                                                                                                                                                                        PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (
                                                                                                                                                                                                                                                                                                                                                                                                                                                         PShDisj (escale 4096 (EVar 246)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (
                                                                                                                                                                                                                                                                                                                                                                                                                                                          PShDisj (escale 4096 (EVar 246)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (
                                                                                                                                                                                                                                                                                                                                                                                                                                                           PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (
                                                                                                                                                                                                                                                                                                                                                                                                                                                            PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (
                                                                                                                                                                                                                                                                                                                                                                                                                                                             PShDisj (escale 4096 (EVar 247)) (ELit 0x10000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (
                                                                                                                                                                                                                                                                                                                                                                                                                                                              PShDisj (escale 4096 (EVar 247)) (ELit 0x10000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (
                                                                                                                                                                                                                                                                                                                                                                                                                                                               PCaseDisjJ (ELit 0x7fff7000) (escale 4096 (EVar 247)) 0x548c8 []  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 294)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  PShDisj (escale 4096 (EVar 361)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   PRun []  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    PMmap  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PSpin  (* [comment removed for export] *))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PShDisj (escale 4096 (EVar 362)) (ELit 0x1000) e_band e_bandlen  (* [comment removed for export] *)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PShDisj (escale 4096 (EVar 362)) (ELit 0x1000) (ELit 0x10000) (ELit 0x61b000)  (* [comment removed for export] *)
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

Definition startup_plan_ranges : list (Z * nat) := [(0x31600, 384%nat); (0x33900, 512%nat); (0x34b00, 192%nat); (0x38200, 128%nat); (0x38700, 192%nat); (0x3d400, 192%nat); (0x3dc00, 128%nat); (0x3e500, 1152%nat); (0x3fd00, 896%nat); (0x41100, 128%nat); (0x41800, 960%nat); (0x43000, 256%nat); (0x47a00, 192%nat); (0x48b00, 192%nat); (0x49a00, 6720%nat); (0x52600, 640%nat); (0x53300, 320%nat); (0x53a00, 128%nat); (0x54500, 448%nat); (0x54f00, 192%nat); (0x55600, 256%nat); (0x59400, 128%nat); (0x59c00, 128%nat); (0x5a000, 320%nat); (0x5a600, 896%nat); (0x5bd00, 128%nat); (0x5c000, 128%nat); (0x5c600, 1152%nat); (0x5e700, 256%nat); (0x5ef00, 256%nat); (0x60700, 128%nat); (0x60e00, 320%nat); (0x61500, 128%nat); (0x61800, 256%nat); (0x62000, 192%nat); (0x62500, 1280%nat); (0x63c00, 1152%nat); (0x64f00, 320%nat); (0x65d00, 192%nat); (0x66100, 512%nat); (0x66b00, 256%nat); (0x67200, 1024%nat); (0x69600, 448%nat); (0x6a100, 896%nat); (0x6b600, 384%nat); (0x6c200, 256%nat); (0x6cb00, 128%nat); (0x6cf00, 640%nat); (0x6db00, 128%nat); (0x6de00, 256%nat); (0x6e300, 384%nat); (0x6ed00, 256%nat); (0x70700, 192%nat); (0x70c00, 256%nat); (0x71700, 192%nat); (0x72f00, 128%nat); (0x73200, 320%nat); (0x73a00, 320%nat); (0x74200, 192%nat); (0x7ac00, 640%nat); (0x7db00, 128%nat); (0x80b00, 256%nat); (0x81500, 128%nat); (0xbba00, 896%nat); (0xbca00, 256%nat); (0xbd300, 128%nat); (0xbd900, 1216%nat); (0xc0e00, 192%nat); (0xc6100, 448%nat); (0xc6a00, 384%nat); (0xc7d00, 128%nat); (0xc8100, 192%nat); (0xc8500, 256%nat); (0xc8d00, 128%nat)]%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
