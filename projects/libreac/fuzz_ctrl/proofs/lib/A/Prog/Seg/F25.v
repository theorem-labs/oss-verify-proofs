(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names changed; 544 of its 583 lines of code are new or changed and 357 lines of the source are left out. *)
(* Segment F25 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x825d4-0x825f0, through the call.
   0x825d4 mv s9,a0 (s9 = r, the parse result); 0x825d8 li a0,1; 0x825dc sb a0,20(s3) (s3 = S(fr): the shadow
   byte at S(fr) + 20 is set to 1, so the byte fr + 160 is addressable); 0x825e0 ld a1,120(s1) (a1 = [A+120] =
   fr + 160); 0x825e4 li a0,-18; 0x825e8 sb a0,0(a1) (the byte 0xee is stored at fr + 160); 0x825ec mv a0,s6
   (a0 = blk = phi + 18); 0x825f0 jal reac_ports_unknown@0x87848.  The callee is composed on its lib/A contract
   (reac_ports_unknown_c.v, a Section Hypothesis) and the segment lands at 0x825f4 with a0 = unk and the byte
   first at fr + 160.  FRA and ENT move across the run (which writes one frame shadow byte, one frame byte and
   the callee's 16-byte stack window) by F24's b7_fra_run / b7_ent_run.  Plain twin: plain/Q02.v. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts F24.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLeaf.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcPorts.

(* A byte range stays addressable across a run that does not touch the shadow bytes of that range. *)
Lemma f25_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HW. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|]. exists b. split; [|exact Hok].
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  pose proof (shadow_of_app _ Happ) as His. pose proof (in_shadow_range _ His) as Hr.
  rewrite Mem.wa_unsigned by lia. exact (HW i Hi).
Qed.

(* A carried byte list as the read the step engine consumes. *)
Lemma f25_rdn : forall m a bs, bytes_at rsegs m a bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (Mem.bytes_at_read rsegs m a bs 0 (length bs) H ltac:(lia) ltac:(lia)) as R.
  rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma f25_one : forall (bs : list byte) d, length bs = 1%nat -> bs = [nth 0 bs d].
Proof. intros [|b [|b' l]] d H; cbn in H; try discriminate. reflexivity. Qed.

(* An address inside the footprint lies in one of its intervals. *)
Lemma f25_in_cases : forall (W : list Frame.ivl) x,
  ~ Frame.outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof. exact b7_in_cases. Qed.

(* The registered globals of the frame API all lie below AC.GT (checked by computation), so none of them shares a
   shadow granule with the frame: their addressability survives the shadow-byte store. *)
Definition f25_ag_ok : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? AC.GT)) AF.frame_AG.

Lemma f25_ag_true : f25_ag_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f25_ag_below : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f25_ag_true (lo, len) Hin) as H.
  apply andb_prop in H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [fst snd] in H1, H2. lia.
Qed.

Section F25.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PU : reac_ports_unknown_contract.

(* The shadow map stays readable and writable across any run that keeps writability. *)
Lemma f25_shadow_keep : forall m m', shadow_rw m -> wmono rsegs m m' -> shadow_rw m'.
Proof.
  intros m m' HS WM a Ha. destruct (HS a Ha) as (Hv & _). pose proof (in_shadow_range a Ha) as Hr.
  split; [exact (WM (wa a) Hv)|].
  apply b7_hi_rd; [unfold in_shadow, LOWMEM_END, HIGHSHADOW_BEG, AC.GT in *; lia | lia|].
  exact (WM (wa a) Hv).
Qed.

Lemma f25_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof. intros m a bs H Hl. pose proof (f25_rdn m a bs H) as R. rewrite Hl in R. exact R. Qed.

(* 0x825d4 -> 0x825f4 on explicit registers: the two stores, the spill load and the call.  The memory after
   each store is kept as a transparent local definition (m1, m2), so the byte written into the frame shadow
   stays linked to the state the call runs on. *)
Lemma f25_evt :
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
    asan_cells m -> shadow_rw m -> addressable m (phi + 18) 20 ->
    (forall i, 0 <= i < 20 ->
       outside [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] (shadow_addr (phi + 18 + i))) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(spv - 16, spv); (fr + 160, fr + 161)] x) ->
    LE.evt rsegs
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
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m spv phi fr aspill sfr rp lo bs -> -> -> -> -> Hphi1 Hphi2 Hfr0 Hfr32 HfrGT Hspv HsfrL
    Hsfra Hfra Haspill Hspaa Hsfrw Hsh160 Happ160 Hdjfs Hdjps Hdjfsp Hdjpsp Hdjpf Hstk Hlo Hwr1 Hwr2 Hq120 Hlen Hbs
    HAC HSW HADp HADsh HOUT.
  assert (Hspu : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  assert (Hm8 : (fr + 160) mod 8 = 0) by (revert Hfr32; Z.div_mod_to_equations; lia).
  assert (Hsfr0 : 0 <= sfr) by (unfold LOWMEM_END in *; lia).
  assert (HfrGT0 : 0 < fr) by (unfold AC.GT in *; lia).
  assert (HS1 : store_ok rsegs m (wa (sfr + 20)) 1 = true).
  { pose proof (Mem.wr_at_store_ok rsegs m (sfr + 20) 1 0 1%nat Hwr1 ltac:(lia) ltac:(cbn; lia)) as H.
    rewrite Z.add_0_r in H. exact H. }
  (* 0x825d4 mv s9,a0 ; 0x825d8 li a0,1 ; 0x825dc sb a0,20(s3) *)
  step. step. step.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bsx) _) =>
      assert (Haa : aa = wa (sfr + 20)) by (first [reflexivity | word_eq_tac | f_equal; lia]);
      assert (HL1 : length bsx = 1%nat) by (first [reflexivity | vm_compute; reflexivity]);
      assert (HV1 : bv_signed (nth 0 bsx (Z_to_bv 8 0)) = 1) by (vm_compute; reflexivity);
      assert (HB1 : bytes_at rsegs (write_to_mem mm aa bsx) (sfr + 20) [nth 0 bsx (Z_to_bv 8 0)])
        by (rewrite Haa; rewrite <- (f25_one bsx (Z_to_bv 8 0) HL1);
            apply Mem.bytes_at_write_same; [lia | rewrite HL1; cbn [Z.of_nat]; lia]);
      assert (MU1 : munch [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] m (write_to_mem mm aa bsx))
        by (rewrite Haa; apply munch_write;
            [ apply munch_refl | lia | rewrite HL1; cbn [Z.of_nat]; lia
            | rewrite HL1; cbn [Z.of_nat inside]; left; lia ]);
      assert (WM1 : wmono rsegs m (write_to_mem mm aa bsx))
        by (apply wmono_write; apply wmono_refl);
      assert (HSTK1 : stk rsegs (write_to_mem mm aa bsx) lo spv)
        by (rewrite Haa; apply Frame.stk_write; [exact Hstk | lia | rewrite HL1; cbn [Z.of_nat]; lia]);
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
  { pose proof (Mem.wr_at_store_ok rsegs m1 (fr + 160) 1 0 1%nat
                  (Frame.wr_at_transport rsegs m m1 (fr + 160) 1 Hwr2 WM1) ltac:(lia) ltac:(cbn; lia)) as H.
    rewrite Z.add_0_r in H. exact H. }
  step. step.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm2 ?aa2 ?bsy) _) =>
      assert (Haa2 : aa2 = wa (fr + 160)) by (first [reflexivity | word_eq_tac | f_equal; lia]);
      assert (HL2 : length bsy = 1%nat) by (first [reflexivity | vm_compute; reflexivity]);
      assert (MU2 : munch [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] m (write_to_mem mm2 aa2 bsy))
        by (rewrite Haa2; apply munch_write;
            [ exact MU1 | lia | rewrite HL2; cbn [Z.of_nat]; lia
            | rewrite HL2; cbn [Z.of_nat inside]; right; left; lia ]);
      assert (WM2 : wmono rsegs m (write_to_mem mm2 aa2 bsy))
        by (apply wmono_write; exact WM1);
      assert (HSTK2 : stk rsegs (write_to_mem mm2 aa2 bsy) lo spv)
        by (rewrite Haa2; apply Frame.stk_write; [exact HSTK1 | lia | rewrite HL2; cbn [Z.of_nat]; lia]);
      assert (HB2 : bytes_at rsegs (write_to_mem mm2 aa2 bsy) (sfr + 20) [b1])
        by (rewrite Haa2; apply (Mem.bytes_at_write_other rsegs mm2 (fr + 160) bsy (sfr + 20) [b1] HB1);
            [ lia | rewrite HL2; cbn [Z.of_nat]; lia
            | rewrite HL2; cbn [length Z.of_nat]; destruct Hdjfs as [Hd|Hd]; lia ]);
      set (m2 := write_to_mem mm2 aa2 bsy) in *
  end.
  (* the callee premises on the memory after the two stores *)
  assert (HAC2 : asan_cells m2).
  { apply (fl_asan_cells [(sfr + 20, sfr + 21); (fr + 160, fr + 161)] m m2 HAC MU2).
    intros x Hx. cbn [outside]. unfold RT_LO, RT_HI, AC.GT, LOWMEM_END in *.
    split; [lia|]. split; [lia | exact I]. }
  assert (HSW2 : shadow_rw m2) by exact (f25_shadow_keep m m2 HSW WM2).
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
  eapply evt_cut.
  { eapply PU with (p := phi + 18) (c := fr + 160) (bs := bs) (lo := lo).
    - first [rewrite MState.unsigned_lit by lia; lia | reflexivity].
    - first [rewrite MState.unsigned_lit by lia; lia | reflexivity].
    - rewrite Hspu. exact HSTK2.
    - rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - intros _. split; [lia|]. split; [exact Hlen|]. split; [exact Hbs2|].
      rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - intros _. split.
      + exact (Frame.wr_at_transport rsegs m m2 (fr + 160) 1 Hwr2 WM2).
      + split; [intros _; destruct Hdjpf as [Hd|Hd]; lia|].
        rewrite Hspu. unfold REAC_PORTS_UNKNOWN_FRAME. lia.
    - exact HAC2.
    - exact HSW2.
    - intros _. exact HADf2.
    - intros _. exact HADp2.
    - intros x Hx. unfold reac_ports_unknown_W. rewrite Hspu.
      replace (fr + 160 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [app]. unfold REAC_PORTS_UNKNOWN_FRAME.
      replace (fr + 160 + 1) with (fr + 161) by lia. exact (HOUT x Hx). }
  intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & m' & -> & MUc & WMc & STc & _ & Hfb).
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ ?pcx _ _ _ _) =>
      replace pcx with (Z_to_bv 64 0x825f4)
        by (symmetry; first [ rewrite ?MState.ret_pc_fold; apply MState.ret_pc_even; lia
                            | apply bv_eq; vm_compute; reflexivity
                            | vm_compute; reflexivity ])
  end.
  assert (Eok : RP.pu_ok (phi + 18) bs = RP.pu_decl bs) by (apply b7_pu_ok; lia).
  rewrite Eok in Hfb |- *.
  rewrite Hspu in MUc.
  apply evt_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, b1, m'.
  split; [reflexivity|].
  split.
  { eapply (munch_trans _ m m2 m').
    - eapply munch_weaken; [|exact MU2]. unfold Frame.sub_fp. cbn [outside].
      intros x (Hx1 & Hx2 & _). split; [exact Hx1|]. split; [exact Hx2 | exact I].
    - eapply munch_weaken; [|exact MUc]. unfold Frame.sub_fp, reac_ports_unknown_W.
      replace (fr + 160 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [app outside]. intros x (Hx1 & Hx2 & Hx3 & _). unfold REAC_PORTS_UNKNOWN_FRAME.
      split; [intros Hc; apply Hx3; lia|]. split; [intros Hc; apply Hx2; lia | exact I]. }
  split; [exact (Frame.wmono_trans rsegs m m2 m' WM2 WMc)|].
  split.
  { eapply fl_bytes; [exact HB2 | exact MUc |].
    cbn [length Z.of_nat]. intros x Hx. unfold reac_ports_unknown_W.
    replace (fr + 160 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [app outside]. unfold REAC_PORTS_UNKNOWN_FRAME.
    split; [lia|]. split; [destruct Hdjfs as [Hd|Hd]; lia | exact I]. }
  split; [exact HV1|].
  unfold b8. exact (Hfb ltac:(lia)).
Qed.

Lemma seg_F25 : forall j : nat, Hat B APIf ra (Inv_A825f4_at B APIf ra) j ->
  Hat B APIf ra (Inv_A825d4_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hjle & HHB & HFLSI & HK & Ha0 & HPORTS &
    HADq).
  subst c. rewrite SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  rewrite Hasz in HFRA, HENT.
  pose proof HK as (HLK & Hs7 & Hs6 & Hphi1 & Hphi2 & Hflen & Hblk & Hsum & Hs8 & H18 & H152 & Hgph & Hph & Hlen &
    HLT & HSPL).
  destruct (b7_fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA)
    as (Happ & HGT & Hfr0 & Hfrhi & Hfr8).
  destruct (b7_fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hwinlo & Hsphi & Hwin).
  destruct (b7_hb_apart B APIf ra g fr phi (flen g j) regs mem md HFRA ltac:(lia)) as (Hhb1 & Hhb2).
  destruct (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HCK & _ & _ & HC4).
  assert (HFN : FN_STACK = 1048576 - 4096) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof (HCK 16 ltac:(lia)) as HC1.
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin0 & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb1 phi (flen g j) ++ g_H g) mem md HAH) as Hhigh.
  assert (HspA : AC.aspZ regs = sp) by exact Haspz.
  rewrite HspA in HC1, Hwin, Hwinlo, Hsphi, Hhb1.
  pose proof Hwin0 as (Hw0 & Hw1 & Hwv).
  assert (HSb : 0 <= g_S g - 104 /\ g_S g <= 2 ^ 64) by lia.
  assert (HAb : 0 <= A /\ A + 416 <= 2 ^ 64) by (unfold HIGHMEM_BEG in *; lia).
  assert (HA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. lia. }
  assert (HA9 : forall A2, getr regs 9 = Z_to_bv 64 A2 -> - 408 <= A2 -> A2 < 2 ^ 64 -> A2 = A).
  { intros A2 H2 Hlo2 Hhi2. unfold rg in Hr9. rewrite H2 in Hr9.
    apply (f_equal (@bv_unsigned 64)) in Hr9. rewrite !MState.unsigned_lit_wrap in Hr9.
    Z.div_mod_to_equations. lia. }
  (* the frame's shadow *)
  assert (HSfr160 : shadow_addr (fr + 160) = Sfr fr + 20).
  { unfold Sfr, shadow_addr. replace (fr + 160) with (fr + 20 * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (HSfr0 : 0 <= Sfr fr).
  { unfold Sfr, shadow_addr, ASAN_K. pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)). lia. }
  assert (HinS : forall k, 0 <= k < FRAME_SHADOW -> in_shadow (Sfr fr + k)).
  { intros k Hk.
    assert (Hdiv : (fr + 8 * k) / 8 = fr / 8 + k).
    { replace (8 * k) with (k * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    pose proof (shadow_of_app (fr + 8 * k) (Happ (fr + 8 * k) ltac:(lia))) as His.
    replace (shadow_addr (fr + 8 * k)) with (Sfr fr + k) in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HSr1 : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (HinS (FRAME_SHADOW - 1) ltac:(lia)) as Hs379.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  assert (HSr2 : LOWMEM_END <= Sfr fr).
  { pose proof (HinS 0 ltac:(lia)) as Hs0.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  assert (HSfrA : Sfr fr + FRAME_SHADOW <= A) by (unfold HIGHMEM_BEG, AF.SLOT_STACK in *; lia).
  assert (Hshapart : forall lo0 hi0, lo0 < hi0 -> (forall x, lo0 <= x < hi0 -> app_mem x) ->
            hi0 <= Sfr fr \/ Sfr fr + FRAME_SHADOW <= lo0).
  { intros lo0 hi0 Hlt Hap.
    pose proof (Hap lo0 ltac:(lia)) as Hal.
    destruct (Z_lt_le_dec lo0 LOWMEM_END) as [Hlo|Hlo].
    - left. destruct (Z_le_gt_dec hi0 LOWMEM_END) as [He|He]; [lia|].
      exfalso. pose proof (Hap LOWMEM_END ltac:(lia)) as Hmid.
      unfold app_mem in Hmid. destruct Hmid as [Hmid|Hmid];
        [lia | unfold LOWMEM_END, HIGHMEM_BEG in Hmid; lia].
    - right. pose proof (Hap lo0 ltac:(lia)) as Hal2.
      unfold app_mem in Hal2. destruct Hal2 as [Hal2|Hal2]; lia. }
  assert (Hfrsh : fr + FRAME_BYTES <= Sfr fr \/ Sfr fr + FRAME_SHADOW <= fr)
    by (apply Hshapart; [lia | intros x Hx; apply Happ; lia]).
  assert (HADphi : addressable mem phi (AC.a_size (flen g j))) by (destruct HHB as (_ & H); exact H).
  pose proof (addressable_app mem phi (AC.a_size (flen g j)) HADphi) as Happhi.
  unfold AC.a_size in Happhi, HADphi.
  assert (Hphsh : phi + 50 <= Sfr fr \/ Sfr fr + FRAME_SHADOW <= phi)
    by (apply Hshapart; [lia | intros x Hx; apply Happhi; lia]).
  set (W := [(Sfr fr + 20, Sfr fr + 21); (fr + 160, fr + 161); (sp - 16, sp)]).
  assert (HWgt : forall lo hi, In (lo, hi) W -> AC.GT <= lo).
  { intros lo hi Hin. unfold W in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-;
      unfold AC.GT, LOWMEM_END, HIGHMEM_BEG, AF.SLOT_STACK in *; lia. }
  assert (HBW : B7W fr sp W).
  { split; [exact HWgt|]. intros x Hx. destruct (f25_in_cases W x Hx) as (lo0 & hi0 & Hin & Hr).
    unfold W in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
    - right. right. exists (fr + 160). split; [lia|]. rewrite HSfr160. lia.
    - right. left. lia.
    - left. unfold AF.SLOT_STACK in *. lia. }
  assert (Happw : forall x, sp - 16 <= x < sp -> app_mem x).
  { intros x Hx. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
  assert (HOUTsh : forall a, 0 <= a -> app_mem a -> ~ (fr + 160 <= a < fr + 168) ->
            outside [(Sfr fr + 20, Sfr fr + 21); (fr + 160, fr + 161); (sp - 16, sp)] (shadow_addr a)).
  { intros a Hz0 Hap Hnb. pose proof (shadow_of_app a Hap) as His.
    cbn [Frame.outside]. split; [|split; [|split; [|exact I]]].
    - intros Hc. apply Hnb.
      assert (Heq : shadow_addr a = shadow_addr (fr + 160)) by (rewrite HSfr160; lia).
      unfold shadow_addr in Heq.
      assert (Hm8 : (fr + 160) mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
      revert Heq Hm8 Hz0. Z.div_mod_to_equations. lia.
    - intros Hc. exact (app_not_shadow (shadow_addr a) ltac:(apply Happ; lia) His).
    - intros Hc. exact (app_not_shadow (shadow_addr a) ltac:(apply Happw; lia) His). }
  assert (HADp : addressable mem (phi + 18) 20)
    by (apply (addressable_sub mem phi (Z.max (flen g j) 1) 18 20 HADphi); lia).
  (* the block's shadow bytes avoid the written frame shadow byte (granule argument) *)
  assert (HADshb : forall i, 0 <= i < Z.max (flen g j) 1 -> outside W (shadow_addr (phi + i))).
  { intros i Hi.
    assert (Hap : app_mem (phi + i)) by (apply Happhi; lia).
    pose proof (shadow_of_app _ Hap) as His.
    unfold W. cbn [Frame.outside]. split; [|split; [|split; [|exact I]]].
    - intros Hc.
      assert (Heq : shadow_addr (phi + i) = shadow_addr (fr + 160)) by (rewrite HSfr160; lia).
      unfold shadow_addr in Heq.
      assert (Hd : (phi + i) / 8 = (fr + 160) / 8) by lia.
      assert (Hm8 : (fr + 160) mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
      assert (Hm : fr + 160 <= phi + i < fr + 168) by (revert Hd Hm8; Z.div_mod_to_equations; lia).
      destruct Hhb2 as [Hd1|Hd1]; lia.
    - intros Hc. exact (app_not_shadow (shadow_addr (phi + i)) ltac:(apply Happ; lia) His).
    - intros Hc. exact (app_not_shadow (shadow_addr (phi + i)) ltac:(apply Happw; lia) His). }
  assert (HADqsh : forall i, 0 <= i < 12 -> outside W (shadow_addr (fr + 128 + i))).
  { intros i Hi.
    assert (Hap : app_mem (fr + 128 + i)) by (apply Happ; lia).
    pose proof (shadow_of_app _ Hap) as His.
    unfold W. cbn [Frame.outside]. split; [|split; [|split; [|exact I]]].
    - intros Hc.
      assert (Heq : shadow_addr (fr + 128 + i) = shadow_addr (fr + 160)) by (rewrite HSfr160; lia).
      unfold shadow_addr in Heq.
      assert (Hm8 : fr mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
      revert Heq Hm8 Hi. Z.div_mod_to_equations. lia.
    - intros Hc. exact (app_not_shadow (shadow_addr (fr + 128 + i)) ltac:(apply Happ; lia) His).
    - intros Hc. exact (app_not_shadow (shadow_addr (fr + 128 + i)) ltac:(apply Happw; lia) His). }
  (* the evt premises that come from the cut *)
  assert (Hwr1 : wr_at rsegs mem (Sfr fr + 20) 1).
  { split; [lia|]. split; [unfold HIGHMEM_BEG, AF.SLOT_STACK in *; lia|]. intros i Hi.
    assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
    exact (proj1 (HSW0 (Sfr fr + 20) (HinS 20 ltac:(lia)))). }
  assert (Hwr2 : wr_at rsegs mem (fr + 160) 1).
  { split; [lia|]. split; [unfold APPMEM_END in *; lia|]. intros i Hi.
    assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
    unfold writable_at in HC4. exact (HC4 (fr + 160) ltac:(lia)). }
  assert (Hq120 : q64 mem (A + 120) (fr + 160)).
  { destruct HSPL as (_ & (A' & HA' & Hq) & _).
    assert (EA : A' = A).
    { unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq.
      apply HA9; [exact HA' | lia | lia]. }
    subst A'. exact Hq. }
  assert (HOUT : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            outside [(sp - 16, sp); (fr + 160, fr + 161)] x).
  { intros x Hx. cbn [outside]. destruct Hx as [Hx|[Hx|Hx]].
    - unfold GOT_CELL_K, AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *. split; [lia|]. split; [lia | exact I].
    - unfold CELL_K, AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *. split; [lia|]. split; [lia | exact I].
    - split; [|split; [|exact I]].
      + intros Hin. exact (app_not_shadow x (Happw x Hin) Hx).
      + intros Hin. exact (app_not_shadow x (Happ x ltac:(lia)) Hx). }
  (* the run *)
  apply (b7_run_lib regs (Z_to_bv 64 0x825d4) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x825f4 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\
       getr R0 20 = getr regs 20 /\ getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\
       getr R0 24 = getr regs 24 /\ getr R0 18 = getr regs 18 /\
       getr R0 25 = Z_to_bv 64 (t_rp (g_in g) j) /\
       getr R0 10 = Z_to_bv 64 (t_unk (g_in g) j) /\
       munch W mem mem' /\ wmono rsegs mem mem' /\
       (exists b1 : byte, bytes_at rsegs mem' (Sfr fr + 20) [b1] /\ bv_signed b1 = 1) /\
       b8 mem' (fr + 160) (t_first (g_in g) j))
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite (b7_mkR_of_expand fx regs). unfold rg in Hs6, Ha0, Hr9, Hr19.
    rewrite Hs6, Ha0, Hr2, Hr9, Hr19.
    eapply LE.evt_mono.
    { eapply f25_evt with (spv := sp) (phi := phi) (fr := fr) (aspill := A) (sfr := Sfr fr)
        (rp := t_rp (g_in g) j) (lo := sp - FN_STACK) (bs := t_pbs (g_in g) j).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - exact Hfrm.
      - exact HGT.
      - unfold APPMEM_END, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
      - unfold LOWMEM_END in *. lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
      - exact HSfr160.
      - apply Happ. lia.
      - exact Hfrsh.
      - exact Hphsh.
      - destruct HC1 as [H|H]; [left | right]; lia.
      - left. lia.
      - destruct Hhb2 as [H|H]; [right | left]; lia.
      - exact Hwin.
      - lia.
      - exact Hwr1.
      - exact Hwr2.
      - exact Hq120.
      - apply b7_pbs_length.
      - apply b7_pbs_bytes. exact Hblk.
      - exact HAC0.
      - exact HSW0.
      - exact HADp.
      - intros i Hi. pose proof (HADshb (18 + i) ltac:(lia)) as Hshb.
        replace (phi + (18 + i)) with (phi + 18 + i) in Hshb by lia.
        unfold W in Hshb. cbn [outside] in Hshb. cbn [outside].
        split; [tauto|]. split; [tauto | exact I].
      - exact HOUT. }
    { intros ms' (ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & b1 & m' & E & MUc & WMc
        & HB1 & HV1 & Hfb).
      eexists _, (Z_to_bv 64 0x825f4), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [unfold t_unk; reflexivity|].
      split; [exact MUc|]. split; [exact WMc|].
      split; [exists b1; split; [exact HB1 | exact HV1]|].
      unfold t_first. exact Hfb. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er20 & Er22 & Er23 &
      Er24 & Er18 & Er25 & Er10 & MU & WM & (b1 & HB1 & HV1) & Hfb) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr25 : getr regs' 25 = Z_to_bv 64 (t_rp (g_in g) j)) by (rewrite Hreg; exact Er25).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (t_unk (g_in g) j)) by (rewrite Hreg; exact Er10).
    assert (Haspz' : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md).
    { apply (b7_fra_run B APIf ra empty FF g fr (hb1 phi (flen g j)) regs regs' mem mem' md W HFRA MU WM);
        [ rewrite HspA; exact HBW | | | | | | | | | | | | ].
      - intros x Hx. unfold W. cbn [outside]. split; [|split; [|split; [|exact I]]].
        + destruct Hfrsh as [H|H]; lia.
        + lia.
        + destruct HC1 as [H|H]; lia.
      - intros A' HA' HA'r x Hx.
        assert (EA : A' = A) by (apply HA9; [exact HA' | lia | lia]). subst A'.
        unfold W. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
      - intros A' HA' HA'r x Hx.
        assert (EA : A' = A) by (apply HA9; [exact HA' | lia | lia]). subst A'.
        unfold W. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
      - intros x Hx. unfold W. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
      - intros a Hin.
        pose proof (f25_ag_below a Hin) as Hab.
        pose proof (HAG a Hin) as HadA.
        apply (addr1_munch W mem mem' a MU); [|exact HadA].
        unfold W. apply HOUTsh; [lia | exact (addr1_app mem a HadA) | unfold AC.GT in *; lia].
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs' regs' mem' md md' HFRA');
        try reflexivity; exact Hmat. }
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md)
      by (apply (b7_ent_run B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md W HENT HFRA MU WM);
          rewrite HspA; exact HBW).
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md')
      by (eapply ent_mat; [exact HENT' | exact Hmat]).
    assert (HOUTfr : forall x, fr <= x < fr + 160 \/ fr + 161 <= x < fr + FRAME_BYTES -> outside W x).
    { intros x Hx. unfold W. cbn [outside]. split; [|split; [|split; [|exact I]]].
      - destruct Hfrsh as [H|H]; lia.
      - lia.
      - destruct HC1 as [H|H]; lia. }
    (* FLSI and B7K: the run writes the shadow byte of fr + 160, the byte fr + 160 and the callee's window *)
    assert (HBW' : B7W fr (AC.aspZ regs) W) by (rewrite HspA; exact HBW).
    assert (HC : FLSI g j fr regs' mem' /\ B7K g j phi fr regs' mem').
    { apply (b7_carry B APIf ra g j phi fr regs regs' mem mem' md W HFRA HHB HFLSI HK MU WM HBW').
      - intros x Hx. apply HOUTfr. right. lia.
      - intros i Hi. unfold W. apply HOUTsh; [lia | apply Happ; lia | lia].
      - intros i Hi. unfold W. apply HOUTsh; [lia | apply Happ; lia | lia].
      - intros i Hi. unfold W, fragb. apply HOUTsh; [lia | apply Happ; lia | lia].
      - intros x Hx. apply HOUTfr. right. lia.
      - intros i Hi. unfold W. apply HOUTsh; [lia | apply Happ; lia | lia].
      - exact Fr9.
      - exact Fr18.
      - exact Fr21.
      - exact Fr22.
      - exact Fr23.
      - exact Fr24. }
    destruct HC as (HFLSI' & HK').
    assert (HKeep : forall a n, (forall x, a <= x < a + n -> outside W x) ->
              forall bs0, Z.of_nat (length bs0) = n -> bytes_at rsegs mem a bs0 -> bytes_at rsegs mem' a bs0).
    { intros a n Hout bs0 Hl Hb. eapply fl_bytes; [exact Hb | exact MU|]. rewrite Hl. exact Hout. }
    assert (HADf' : addressable mem' (fr + 160) 1).
    { split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|].
      intros i Hi. assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
      split; [apply Happ; lia|]. exists b1. split.
      - rewrite HSfr160. destruct HB1 as (_ & _ & HB1'). pose proof (HB1' 0%nat ltac:(cbn; lia)) as HE.
        cbn [Z.of_nat] in HE. rewrite Z.add_0_r in HE. exact HE.
      - unfold shadow_ok. rewrite HV1. right.
        assert (Hm8 : (fr + 160) mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia). lia. }
    assert (HexA : Inv_A825f4_at B APIf ra g j
             (mkCfg (mkst regs' (Z_to_bv 64 0x825f4) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      rewrite ?Hasz.
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|].
      split; [exact Hjle|].
      split.
      { destruct HHB as (Hnz & HAD). split; [exact Hnz|].
        apply (f25_addr_keep W mem mem' phi (Z.max (flen g j) 1) HAD MU HADshb). }
      split; [exact HFLSI'|].
      split; [exact HK'|].
      split; [unfold rg; exact Fr25|].
      split; [unfold rg; exact Fr10|].
      split.
      { unfold PORTS in *. destruct HPORTS as (Hz & Hnz). split; intros E.
        - destruct (Hz E) as (Q0 & Q4 & Q8). unfold u32 in *.
          split; [apply (HKeep (fr + 128) 4); [intros x Hx; apply HOUTfr; left; lia | rewrite length_le4; reflexivity | exact Q0]|].
          split; [apply (HKeep (fr + 132) 4); [intros x Hx; apply HOUTfr; left; lia | rewrite length_le4; reflexivity | exact Q4]
                 | apply (HKeep (fr + 136) 4); [intros x Hx; apply HOUTfr; left; lia | rewrite length_le4; reflexivity | exact Q8]].
        - destruct (Hnz E) as (Q0 & Q4 & Q8). unfold u32 in *.
          split; [apply (HKeep (fr + 128) 4); [intros x Hx; apply HOUTfr; left; lia | rewrite length_le4; reflexivity | exact Q0]|].
          split; [apply (HKeep (fr + 132) 4); [intros x Hx; apply HOUTfr; left; lia | rewrite length_le4; reflexivity | exact Q4]
                 | apply (HKeep (fr + 136) 4); [intros x Hx; apply HOUTfr; left; lia | rewrite length_le4; reflexivity | exact Q8]]. }
      split; [exact Hfb|].
      split; [apply (f25_addr_keep W mem mem' (fr + 128) 12 HADq MU HADqsh)|].
      exact HADf'. }
    pose proof (Hexit g _ HexA) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F25.
