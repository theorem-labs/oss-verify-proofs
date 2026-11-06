(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec Mem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegVCx SegDig SegDigOk.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SFPCU_sum PFFCU_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegU2 Require Import S2TabU S2SumHU U2N_defs U2N_cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition gpu2n (data idxs : list Z) : nat -> list word -> (word -> option byte) -> Prop := SDG.gpx SG (gp2 SG data idxs).

Section U2NS.
  Hypothesis SFPCSU_ok : forall GP, SP.summ_ok SG GP SFPCSU.
  Hypothesis PFFCSU_ok : forall GP, SP.summ_ok SG GP PFFCSU.

  Theorem u2n_sound : forall data idxs T E M rom ms, In T (SP.p_tm U2N ++ SP.p_xt U2N) -> rom = seg_rom usegs -> mem_inv usegs M ->
    SX.aw_genuine E (SP.p_A U2N) -> ST.tm_okF SG T E M rom ms -> SG.gholds (gpu2n data idxs) E M (ST.t_ghost T) ->
    exists ms', ExecF.mstepsF SG (SX.fp_of (SP.p_A U2N) E) ms ms' /\
      SP.prun_postH SG (gpu2n data idxs) MMU.hmH MMU.hmA U2N E M rom ms'.
  Proof.
    intros data idxs T E M rom ms HinT HRom HMI HAG HT HG.
    exact (SP.pcheck_soundH SG (gpu2n data idxs) (SDG.gfpx gfp2)
             (SVX.gvc_enrich SVX.bc_enrich (SDG.gsplit SG (wvc_ok SG 1048512 0x13768)))
             (SDG.gpx_frame SG (gp2 SG data idxs) gfp2 (gp2_frame SG data idxs))
             (SVX.gvc_enrich_ok SG (gpu2n data idxs) SVX.bc_enrich _ (SVX.bc_enrich_ok SG)
                (SDGok.gsplit_ok SG (gp2 SG data idxs) _ (wvc_ok_sound SG data idxs 1048512 ltac:(lia) 0x13768 ltac:(lia) d2v_img_ubsan)))
             MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF U2N U2N_IT 4000 true U2N_hints (fun _ => True)
             (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ u2n_cert) (SP.itab_ranges_sound SG _) ltac:(intros TA [])
             ltac:(intros Sm HSm; cbn [SP.p_cs U2N] in HSm;
                   destruct HSm as [<-|[<-|[<-|[<-|[]]]]];
                   [ apply MMU.mcpu_ok; lia | apply MMU.msp_ok; lia
                   | apply summ_okH_of_okU; [reflexivity | apply SFPCSU_ok]
                   | apply summ_okH_of_okU; [reflexivity | apply PFFCSU_ok] ])
             ltac:(intros; exact I) ltac:(intros; unfold SP.wins_client; apply Forall_forall; intros; exact I)
             ltac:(intros E0 _ w Hw; destruct Hw) ltac:(intros; constructor)
             T E M rom ms HinT HRom HAG I HMI HT HG).
  Qed.
End U2NS.
Print Assumptions u2n_sound.
