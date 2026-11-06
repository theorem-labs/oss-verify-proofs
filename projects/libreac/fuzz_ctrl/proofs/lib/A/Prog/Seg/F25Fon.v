(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names changed; 544 of its 583 lines of code are new or changed and 357 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F25.v; 59 of its 220 lines of code are new or changed and 422 lines of the source are left out. *)
(* lib/A/Prog/Seg/F25Fon.v -- route (C) twin of Seg/F25F.v's (not in this delivery) f25_evt_F (a Theorem Labs lane 12:52Z twin rule: an ADDITIVE
   beside-file; Seg/F25F.v (not in this delivery) stays byte-identical).  Writer: a Theorem Labs lane, for glue stage seg_F25.
   proves no function (kind: segment lemma).

   BASE: Seg/F25F.v (not in this delivery) at a Theorem Labs lane's fold a working branch 4bae33fdf54 (blob ee74bb6ffb9), not the
   blob 60ad0f4dc03 of a working branch: the two differ only in the fold's full qualification of the twin-library lemmas
   (A.Tk.UL.MState / Mem / Frame), which this file keeps.

   THE CHANGE, and only it: f25_evt_F's premise `shadow_rw m` is REMOVED, and its callee premise
   reac_ports_unknown_contract_F becomes reac_ports_unknown_contract_F_on (LANDED.md (a working note, not in this delivery): a Theorem Labs lane d4f70537e6f, proof
   a Theorem Labs lane 4038362e590 reac_ports_unknown_F_holds_on).  Why removed, not narrowed: the run 0x825d4 -> 0x825f4 STORES one shadow
   byte (0x825dc, sb to S(fr) + 20), which it justifies from its own premise `wr_at rsegs m (sfr + 20) 1`, and READS
   no shadow byte; its only use of `shadow_rw m` in f25_evt_F was to carry it to the memory after the two stores
   (f25_shadow_keep) and feed the callee's premise there, which the _on contract drops.  The post is unchanged. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts F24 F25.
(* Last: StepF's step / if_false / finish (evtF goals) shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr, as F25.v does. *)
Import YK11.
Local Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcPorts.

(* ---- f25_evt_F with no shadow premise, on the callee's route (C) contract. ---- *)
Lemma f25_evt_F_on :
  forall (RNG : ExecF.footprint),
    reac_ports_unknown_contract_F_on ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv phi fr aspill sfr rp lo : Z) (bs : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 aspill -> s3 = Z_to_bv 64 sfr ->
    s6 = Z_to_bv 64 (phi + 18) -> a0 = Z_to_bv 64 rp ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= fr -> fr mod 32 = 0 -> AC.GT <= fr ->
    0 <= spv < 2 ^ 64 ->
    LOWMEM_END <= sfr -> sfr + FRAME_SHADOW <= aspill -> fr + FRAME_BYTES <= aspill -> aspill + 416 <= 2 ^ 64 ->
    spv <= aspill -> sfr + FRAME_SHADOW <= spv - 16 ->
    shadow_addr (fr + 160) = sfr + 20 -> app_mem (fr + 160) ->
    (fr + FRAME_BYTES <= sfr \/ sfr + FRAME_SHADOW <= fr) ->
    (phi + 50 <= sfr \/ sfr + FRAME_SHADOW <= phi) ->
    (fr + FRAME_BYTES <= spv - 16 \/ spv <= fr) ->
    (phi + 38 <= spv - 16 \/ spv <= phi + 18) ->
    (fr + 161 <= phi + 18 \/ phi + 38 <= fr + 160) ->
    stk rsegs m lo spv -> lo + 16 <= spv ->
    wr_at rsegs m (sfr + 20) 1 -> wr_at rsegs m (fr + 160) 1 ->
    q64 m (aspill + 120) (fr + 160) ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    asan_cells m -> addressable m (phi + 18) 20 ->
    (forall i, 0 <= i < 20 ->
       outside [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] (shadow_addr (phi + 18 + i))) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(spv - 16, spv); (fr + 160, fr + 161)] x) ->
    ExecF.rng RNG (sfr + 20) 1 ->
    ExecF.rng RNG (fr + 160) 1 ->
    ExecF.rng RNG (aspill + 120) 8 ->
    ExecF.rng RNG (phi + 18) 20 ->
    ExecF.rng RNG (shadow_addr (phi + 18)) (shadow_addr (phi + 18 + 19) - shadow_addr (phi + 18) + 1) ->
    ExecF.rng RNG (spv - 16) 16 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' : word) (b1 : byte)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if RP.pu_decl bs then 4 * RP.pu_nunk bs 12 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 rp) s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x825f4) fc None m' (seg_rom rsegs) /\
         munch [(sfr + 20, sfr + 21); (fr + 160, fr + 161); (spv - 16, spv)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (sfr + 20) [b1] /\ bv_signed b1 = 1 /\
         b8 m' (fr + 160) (if RP.pu_decl bs then RP.pu_first bs 12 else 0))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825d4) fc None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros RNG PU ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m spv phi fr aspill sfr rp lo bs -> -> -> -> -> Hphi1 Hphi2 Hfr0 Hfr32 HfrGT Hspv HsfrL
    Hsfra Hfra Haspill Hspaa Hsfrw Hsh160 Happ160 Hdjfs Hdjps Hdjfsp Hdjpsp Hdjpf Hstk Hlo Hwr1 Hwr2 Hq120 Hlen Hbs
    HAC HADp HADsh HOUT RS20 RF160 RQ120 RP20 RSHp RFR RGOT RCK.
  assert (Hspu : bv_unsigned (Z_to_bv 64 spv) = spv) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (Hm8 : (fr + 160) mod 8 = 0) by (revert Hfr32; Z.div_mod_to_equations; lia).
  assert (Hsfr0 : 0 <= sfr) by (unfold LOWMEM_END in *; lia).
  assert (HfrGT0 : 0 < fr) by (unfold AC.GT in *; lia).
  assert (HS1 : store_ok rsegs m (wa (sfr + 20)) 1 = true).
  { pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_store_ok rsegs m (sfr + 20) 1 0 1%nat
    Hwr1 ltac:(lia) ltac:(cbn; lia)) as H.
    rewrite Z.add_0_r in H. exact H. }
  (* 0x825d4 mv s9,a0 ; 0x825d8 li a0,1 ; 0x825dc sb a0,20(s3) *)
  step. step. step.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bsx) _) =>
      assert (Haa : aa = wa (sfr + 20)) by (first [reflexivity | word_eq_tac | f_equal; lia]);
      assert (HL1 : length bsx = 1%nat) by (first [reflexivity | vm_compute; reflexivity]);
      assert (HV1 : bv_signed (nth 0 bsx (Z_to_bv 8 0)) = 1) by (vm_compute; reflexivity);
      assert (HB1 : bytes_at rsegs (write_to_mem mm aa bsx) (sfr + 20) [nth 0 bsx (Z_to_bv 8 0)])
        by (rewrite Haa; rewrite <- (f25_one bsx (Z_to_bv 8 0) HL1);
            apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_write_same; [lia | rewrite HL1;
              cbn [Z.of_nat]; lia]);
      assert (MU1 : munch [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] m (write_to_mem mm aa bsx))
        by (rewrite Haa; apply munch_write;
            [ apply munch_refl | lia | rewrite HL1; cbn [Z.of_nat]; lia
            | rewrite HL1; cbn [Z.of_nat inside]; left; lia ]);
      assert (WM1 : wmono rsegs m (write_to_mem mm aa bsx))
        by (apply wmono_write; apply wmono_refl);
      assert (HSTK1 : stk rsegs (write_to_mem mm aa bsx) lo spv)
        by (rewrite Haa; apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.stk_write;
          [exact Hstk | lia | rewrite HL1; cbn [Z.of_nat]; lia]);
      set (b1 := nth 0 bsx (Z_to_bv 8 0)) in HV1, HB1 |- *;
      set (m1 := write_to_mem mm aa bsx) in *
  end.
  (* 0x825e0 ld a1,120(s1) *)
  assert (HR1 : ov_read_bytes rsegs m1 (wa (aspill + 120)) 8 = Some (le8 (Z_to_bv 64 (fr + 160)))).
  { apply f25_rd8; [|apply length_le8].
    unfold q64 in Hq120. eapply fl_bytes; [exact Hq120 | exact MU1 |].
    rewrite length_le8. intros x Hx. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  step.
  (* 0x825e4 li a0,-18 ; 0x825e8 sb a0,0(a1) *)
  assert (HS2 : store_ok rsegs m1 (wa (fr + 160)) 1 = true).
  { pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wr_at_store_ok rsegs m1 (fr + 160) 1 0 1%nat
                  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wr_at_transport rsegs m m1 (fr + 160) 1
                    Hwr2 WM1) ltac:(lia) ltac:(cbn; lia)) as H.
    rewrite Z.add_0_r in H. exact H. }
  step. step.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm2 ?aa2 ?bsy) _) =>
      assert (Haa2 : aa2 = wa (fr + 160)) by (first [reflexivity | word_eq_tac | f_equal; lia]);
      assert (HL2 : length bsy = 1%nat) by (first [reflexivity | vm_compute; reflexivity]);
      assert (MU2 : munch [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] m (write_to_mem mm2 aa2 bsy))
        by (rewrite Haa2; apply munch_write;
            [ exact MU1 | lia | rewrite HL2; cbn [Z.of_nat]; lia
            | rewrite HL2; cbn [Z.of_nat inside]; right; left; lia ]);
      assert (WM2 : wmono rsegs m (write_to_mem mm2 aa2 bsy))
        by (apply wmono_write; exact WM1);
      assert (HSTK2 : stk rsegs (write_to_mem mm2 aa2 bsy) lo spv)
        by (rewrite Haa2; apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.stk_write;
          [exact HSTK1 | lia | rewrite HL2; cbn [Z.of_nat]; lia]);
      assert (HB2 : bytes_at rsegs (write_to_mem mm2 aa2 bsy) (sfr + 20) [b1])
        by (rewrite Haa2; apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_write_other rsegs
          mm2 (fr + 160) bsy (sfr + 20) [b1] HB1);
            [ lia | rewrite HL2; cbn [Z.of_nat]; lia
            | rewrite HL2; cbn [length Z.of_nat]; destruct Hdjfs as [Hd|Hd]; lia ]);
      set (m2 := write_to_mem mm2 aa2 bsy) in *
  end.
  (* the callee premises on the memory after the two stores *)
  assert (HAC2 : asan_cells m2).
  { apply (fl_asan_cells [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] m m2 HAC MU2).
    intros x Hx. cbn [outside]. unfold RT_LO, RT_HI, AC.GT, LOWMEM_END in *.
    split; [lia|]. split; [lia | exact I]. }
  assert (Hbs2 : bytes_at rsegs m2 (phi + 18) bs).
  { eapply fl_bytes; [exact Hbs | exact MU2 |]. rewrite Hlen. intros x Hx. cbn [outside].
    split; [destruct Hdjps as [Hd|Hd]; lia|].
    split; [destruct Hdjpf as [Hd|Hd]; lia | exact I]. }
  assert (HADp2 : addressable m2 (phi + 18) 20).
  { apply (f25_addr_keep [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] m m2 (phi + 18) 20 HADp MU2).
    intros i Hi. exact (HADsh i Hi). }
  assert (HADf2 : addressable m2 (fr + 160) 1).
  { split; [lia|]. split; [lia|]. split.
    - unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Happ160. unfold APPMEM_END. lia.
    - intros i Hi. assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
      split; [exact Happ160|].
      exists b1. split.
      + rewrite Hsh160. destruct HB2 as (_ & _ & HB2'). pose proof (HB2' 0%nat ltac:(cbn; lia)) as HE.
        cbn [Z.of_nat] in HE. rewrite Z.add_0_r in HE. exact HE.
      + unfold shadow_ok. rewrite HV1. right. lia. }
  (* 0x825ec mv a0,s6 ; 0x825f0 jal reac_ports_unknown *)
  step. step.
  eapply ExecF.evtF_cut.
  { eapply PU with (p := phi + 18) (c := fr + 160) (bs := bs) (lo := lo) (RNG := RNG).
    - first [rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia;
      lia | reflexivity].
    - first [rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia;
      lia | reflexivity].
    - rewrite Hspu. exact HSTK2.
    - rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - intros _. split; [lia|]. split; [exact Hlen|]. split; [exact Hbs2|].
      rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - intros _. split.
      + exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wr_at_transport rsegs m m2 (fr + 160) 1 Hwr2
        WM2).
      + split; [intros _; destruct Hdjpf as [Hd|Hd]; lia|].
        rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - exact HAC2.
    - intros _. exact HADf2.
    - intros _. exact HADp2.
    - intros x Hx. unfold reac_ports_unknown_W. rewrite Hspu.
      replace (fr + 160 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [app]. unfold REAC_PORTS_UNKNOWN_FRAME.
      replace (fr + 160 + 1) with (fr + 161) by lia. exact (HOUT x Hx).
    - rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. exact RFR.
    - exact RGOT.
    - exact RCK.
    - intros _. split; [exact RP20 | exact RSHp].
    - intros _. split; [exact RF160 | rewrite Hsh160; exact RS20]. }
  intros ms' PO. unfold reac_ports_unknown_post in PO.
  destruct PO as (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & m' & -> & MUc & WMc & STc & _ & Hfb).
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ ?pcx _ _ _ _) =>
      replace pcx with (Z_to_bv 64 0x825f4)
        by (symmetry; first [ rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_fold;
          apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_even; lia
                            | apply bv_eq; vm_compute; reflexivity
                            | vm_compute; reflexivity ])
  end.
  assert (Eok : RP.pu_ok (phi + 18) bs = RP.pu_decl bs) by (apply b7_pu_ok; lia).
  rewrite Eok in Hfb |- *.
  rewrite Hspu in MUc.
  apply ExecF.evtF_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, b1, m'.
  split; [reflexivity|].
  split.
  { eapply (munch_trans _ m m2 m').
    - eapply munch_weaken; [|exact MU2]. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.sub_fp.
      cbn [outside].
      intros x (Hx1 & Hx2 & _). split; [exact Hx1|]. split; [exact Hx2 | exact I].
    - eapply munch_weaken; [|exact MUc].
      unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.sub_fp, reac_ports_unknown_W.
      replace (fr + 160 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [app outside]. intros x (Hx1 & Hx2 & Hx3 & _). unfold REAC_PORTS_UNKNOWN_FRAME.
      split; [intros Hc; apply Hx3; lia|]. split; [intros Hc; apply Hx2; lia | exact I]. }
  split; [exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono_trans rsegs m m2 m' WM2 WMc)|].
  split.
  { eapply fl_bytes; [exact HB2 | exact MUc |].
    cbn [length Z.of_nat]. intros x Hx. unfold reac_ports_unknown_W.
    replace (fr + 160 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [app outside]. unfold REAC_PORTS_UNKNOWN_FRAME.
    split; [lia|]. split; [destruct Hdjfs as [Hd|Hd]; lia | exact I]. }
  split; [exact HV1|].
  unfold b8. exact (Hfb ltac:(lia)).
Qed.
