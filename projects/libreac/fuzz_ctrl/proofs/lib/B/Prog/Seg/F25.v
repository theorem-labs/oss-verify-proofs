(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2065 of its 2181 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3.v, with its module paths, module names, addresses and numbers changed; 415 of its 490 lines of code are new or changed and 2106 lines of the source are left out. *)
(* Segment F25 of the target's entry function (fuzz_ctrl LLVMFuzzerTestOneInput, asan-ubsan, patched image B),
   0x82888-0x828a0 (slot-plan-asan-ubsan section 2 row F25, call PU@0x828a0, twin Q02; no FAIL, trap or
   instrumented-check rows), through the call to its return point 0x828a4 (F26's entry).
     0x82888  mv   s9,a0       s9 = r = t_rp (the result of reac_ports_parse at 0x82884)
     0x8288c  sb   s7,20(s3)   shadow byte S(fr) + 20 = s7 = 1 (F23's 0x82874 li s7,1): the granule
                               [fr + 160, fr + 168) has its first byte marked usable
     0x82890  ld   a1,136(s1)  a1 = [A + 136] = fr + 160 (the spill FLI carries)
     0x82894  li   a0,-18
     0x82898  sb   a0,0(a1)    [fr + 160] = 0xee, a plain frame store (the callee writes this byte again)
     0x8289c  mv   a0,s6       a0 = blk = phi + 18 (s6 = [A + 312], 0x82878)
     0x828a0  jal  reac_ports_unknown
   The range has no branch and no instrumented check (a load of the shadow byte and a compare). The callee contract
   (lib/B/Prog/reac_ports_unknown_c.v) is the Section Hypothesis HPU: with p = blk <> 0 and c = fr + 160 <> 0 it
   reads the 20 ports bytes [phi + 18, phi + 38) (addressable: they are inside the live block Phi) and the one byte
   c (addressable: the shadow store 0x8288c marked it usable), returns a0 = t_unk, keeps s0-s11, writes only its 16
   stack bytes [sp - 16, sp) and the byte c, and leaves at c the first-byte value t_first (FIRSTb). The error path of
   the memory-checking runtime inside the callee is not reached because both ranges are addressable.
   The segment's write set is W = [S(fr) + 20, S(fr) + 21) (a frame shadow byte), [fr + 160, fr + 161) (a frame body
   byte) and [sp - 16, sp) (the callee's window). FRA and ENT cross it by Tac_f23.tf_fra_ent (which rebuilds the
   frame's 392-byte shadow list), then move to the post registers and model by Tac_slot.sl_fra_move / ent_mat.
   Entry cut: the official Inv_B82888_at of lib/B/Prog/SlotInv.v. Exit cut: the official Inv_B828a4_at (F27K, FTL,
   s9 = r, a0 = t_unk, s6 = blk, PORTS, FIRSTb, FTURN, IFS (S j) and, last, s5 = fr + 128). Statement: S_F25 of the
   assembly forms. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_f23.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
(* The run is stated in the lib/Lib engine: the callee contract and Tac_f23's memory helpers speak it. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
Import ListNotations.
(* lib.Prog's RcFrag chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this
   file's registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module PUC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ports_unknown_c.

(* The callee's write set with an output byte c <> 0: its 16 stack bytes and the byte c. *)
Lemma f25_PUW : forall s c, c <> 0 -> PUC.reac_ports_unknown_W s c = [(s - 16, s); (c, c + 1)].
Proof.
  intros s c Hc. unfold PUC.reac_ports_unknown_W, PUC.REAC_PORTS_UNKNOWN_FRAME.
  replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc). reflexivity.
Qed.

(* The callee's first-byte value for p <> 0 is the model's t_first (pu_ok p bs = pu_decl bs when p <> 0). *)
Lemma f25_pu_first : forall inp j p, p <> 0 ->
  (if RcPorts.pu_ok p (t_pbs inp j) then RcPorts.pu_first (t_pbs inp j) 12 else 0) = t_first inp j.
Proof.
  intros inp j p Hp. unfold RcPorts.pu_ok, t_first.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp). reflexivity.
Qed.

(* The callee's result for p <> 0 is the model count t_unk (pu_ok p bs = pu_decl bs when p <> 0). *)
Lemma f25_pu_ok : forall inp j p, p <> 0 ->
  (if RcPorts.pu_ok p (t_pbs inp j) then 4 * RcPorts.pu_nunk (t_pbs inp j) 12 else -1) = t_unk inp j.
Proof.
  intros inp j p Hp. unfold RcPorts.pu_ok, t_unk.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp). reflexivity.
Qed.

(* A one-byte store list in its le1 form. *)
Lemma f25_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

(* The segment's write set: the shadow byte S3 + 20, the frame byte D, the callee's 16 stack bytes below sp. *)
Definition f25_W (S3 D sp : Z) : list (Z * Z) := [(S3 + 20, S3 + 21); (D, D + 1); (sp - 16, sp)].

Lemma f25_inW : forall S3 D sp q, ~ outside (f25_W S3 D sp) q ->
  (S3 + 20 <= q < S3 + 21) \/ (D <= q < D + 1) \/ (sp - 16 <= q < sp).
Proof.
  intros S3 D sp q H. unfold f25_W in H. cbn [outside] in H.
  destruct (Z_lt_le_dec q (S3 + 20)) as [H1|H1]; destruct (Z_lt_le_dec q (S3 + 21)) as [H2|H2];
  destruct (Z_lt_le_dec q D) as [H3|H3]; destruct (Z_lt_le_dec q (D + 1)) as [H4|H4];
  destruct (Z_lt_le_dec q (sp - 16)) as [H5|H5]; destruct (Z_lt_le_dec q sp) as [H6|H6];
  first [ left; lia | right; left; lia | right; right; lia | exfalso; apply H; repeat split; lia ].
Qed.

(* The callee's write set (the stack window and the byte D) is inside the segment's. *)
Lemma f25_sub : forall S3 D sp, sub_fp [(sp - 16, sp); (D, D + 1)] (f25_W S3 D sp).
Proof. intros S3 D sp x Hx. unfold f25_W in Hx. cbn [outside] in Hx |- *. tauto. Qed.

(* The three ports words [fr + 128, fr + 140) survive a write set that misses them. *)
Lemma f25_ports_keep : forall g fr j m m' W,
  PORTS g fr j m -> munch W m m' -> (forall x, fr + 128 <= x < fr + 140 -> outside W x) -> PORTS g fr j m'.
Proof.
  intros g fr j m m' W (HP0 & HP1) MU HW. split.
  - intros E. destruct (HP0 E) as (Ha & Hb & Hc). unfold u32 in *.
    split; [|split].
    + eapply fl_bytes; [exact Ha | exact MU |]. rewrite length_le4. intros x Hx. apply HW. lia.
    + eapply fl_bytes; [exact Hb | exact MU |]. rewrite length_le4. intros x Hx. apply HW. lia.
    + eapply fl_bytes; [exact Hc | exact MU |]. rewrite length_le4. intros x Hx. apply HW. lia.
  - intros E. destruct (HP1 E) as (Ha & Hb & Hc). unfold u32 in *.
    split; [|split].
    + eapply fl_bytes; [exact Ha | exact MU |]. rewrite length_le4. intros x Hx. apply HW. lia.
    + eapply fl_bytes; [exact Hb | exact MU |]. rewrite length_le4. intros x Hx. apply HW. lia.
    + eapply fl_bytes; [exact Hc | exact MU |]. rewrite length_le4. intros x Hx. apply HW. lia.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract of reac_ports_unknown (lib/B/Prog/reac_ports_unknown_c.v). *)
Hypothesis HPU : PUC.reac_ports_unknown_contract.

(* The steps 0x82888 -> 0x828a0 and the call, on explicit registers (s3 = S3, s1 = A, s6 = p, s7 = 1, sp = sp). The
   two stores write the shadow byte S3 + 20 = 1 and the byte D = 0xee; the load reads the spill [A + 136, A + 144) =
   D. The callee then reads the ports bytes [p, p + 20) and the byte D, and writes [sp - 16, sp) and D. *)
Lemma f25_evt :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 A D p sp lo : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x9 = Z_to_bv 64 A -> x22 = Z_to_bv 64 p -> x23 = Z_to_bv 64 1 -> bv_unsigned x2 = sp ->
    LOWMEM_END <= S3 + 20 < HIGHMEM_BEG -> shadow_addr D = S3 + 20 -> D mod 8 = 0 -> app_mem D -> 0 < D ->
    wr_at rsegs m (S3 + 20) 1 -> wr_at rsegs m D 1 ->
    0 <= A -> A + 144 <= 2 ^ 64 -> S3 + 21 <= A -> bytes_at rsegs m (A + 136) (le8 (Z_to_bv 64 D)) ->
    0 < p -> p + 20 <= 2 ^ 64 -> length bs = 20%nat -> bytes_at rsegs m p bs -> addressable m p 20 ->
    (forall i, 0 <= i < 20 -> shadow_addr (p + i) <> S3 + 20) ->
    (S3 + 21 <= p \/ p + 20 <= S3 + 20) -> (D + 1 <= p \/ p + 20 <= D) ->
    stk rsegs m lo sp -> lo + 16 <= sp -> HIGHMEM_BEG <= lo ->
    (p + 20 <= sp - 16 \/ sp <= p) -> (D + 1 <= sp - 16 \/ sp <= D) ->
    asan_cells m -> shadow_rw m -> RT_HI <= D -> GOT_CELL_K + 8 <= D -> CELL_K + 8 <= D ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (pc' : word) m',
         ms' = MS R Fr pc' fc None m' (seg_rom rsegs) /\ pc' = Z_to_bv 64 0x828a4 /\
         getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
         getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\ getr R 22 = x22 /\
         getr R 24 = x24 /\
         getr R 25 = x10 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
         getr R 10 = Z_to_bv 64 (if RcPorts.pu_ok p bs then 4 * RcPorts.pu_nunk bs 12 else -1) /\
         munch (f25_W S3 D sp) m m' /\ wmono rsegs m m' /\ stk rsegs m' lo sp /\ b8 m' (S3 + 20) 1 /\
         bytes_at rsegs m' D [Z_to_bv 8 (if RcPorts.pu_ok p bs then RcPorts.pu_first bs 12 else 0)])
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 A D p sp lo bs -> -> -> -> Hsp HS3 HshD HD8 HappD HD0 HWR20 HWRD HA0 HA1 HSA H136
    Hp0 Hp1 Hlen Hbs Hadp Hshp HdjSp HdjDp Hstk Hlo16 Hlohi HdjpW HdjDW HAC HSW HRTD HGOT HCELL.
  assert (HLM : LOWMEM_END = 2147450880) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAEv : APPMEM_END = 140737488355328) by reflexivity.
  pose proof HappD as HDr. unfold app_mem in HDr.
  (* 0x82888 mv s9,a0 *)
  step.
  (* 0x8288c sb s7,20(s3): the shadow byte S3 + 20 becomes 1 (store_ok from the runtime's shadow map) *)
  assert (HS20 : store_ok rsegs m (wa (S3 + 20)) 1 = true).
  { pose proof (wr_at_store_ok rsegs m (S3 + 20) 1 0 1%nat HWR20 ltac:(lia) ltac:(cbn; lia)) as HH.
    rewrite Z.add_0_r in HH. exact HH. }
  step.
  (* the spill [A + 136, A + 144) lies above the shadow byte S3 + 20, so it reads back after the store; the frame
     byte D stays writable after it *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (RD136 : ov_read_bytes rsegs m1 (wa (A + 136)) 8 = Some (le8 (Z_to_bv 64 D)));
    [ apply tf_rd8; [ apply bytes_at_write_other; [ exact H136 | lia | simpl_sizes; lia | simpl_sizes; lia ]
                    | apply length_le8 ]
    | assert (HSD : store_ok rsegs m1 (wa D) 1 = true);
      [ pose proof (wr_at_store_ok rsegs m1 D 1 0 1%nat ltac:(apply wr_at_write; exact HWRD)
                      ltac:(lia) ltac:(cbn; lia)) as HH;
        rewrite Z.add_0_r in HH; exact HH
      | ] ]
  end.
  (* 0x82890 ld a1,136(s1): a1 = D ; 0x82894 li a0,-18 *)
  step. step.
  (* 0x82898 sb a0,0(a1): the plain frame store [D] = 0xee *)
  step.
  (* 0x8289c mv a0,s6 ; 0x828a0 jal reac_ports_unknown *)
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) => pose (mm := m2); change m2 with mm end.
  (* the memory after the two stores *)
  assert (MU2 : munch (f25_W S3 D sp) m mm).
  { subst mm. unfold f25_W.
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl. }
  assert (WM2 : wmono rsegs m mm) by (subst mm; repeat apply wmono_write; apply wmono_refl).
  assert (ST2 : stk rsegs mm lo sp).
  { subst mm. repeat (apply stk_write; [ | lia | simpl_sizes; lia ]). exact Hstk. }
  assert (WRD2 : wr_at rsegs mm D 1) by (subst mm; repeat apply wr_at_write; exact HWRD).
  assert (BS2 : bytes_at rsegs mm p bs).
  { subst mm. repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | rewrite Hlen; simpl_sizes; lia ]).
    exact Hbs. }
  assert (B20 : b8 mm (S3 + 20) 1).
  { subst mm. apply tf_wother.
    - first [ reflexivity | simpl_sizes; reflexivity ].
    - apply tf_wsame; [ first [ reflexivity | vm_compute; reflexivity
                              | rewrite f25_le1, unsigned_lit by lia; reflexivity ] | lia | lia ].
    - lia.
    - lia.
    - lia. }
  (* the runtime's shadow map stays readable: the one shadow byte written reads 1, the rest is unchanged *)
  assert (SW2 : shadow_rw mm).
  { intros a Hin. destruct (HSW a Hin) as (Hw & b & Hb). split; [exact (WM2 (wa a) Hw)|].
    assert (Hab : LOWMEM_END <= a < HIGHMEM_BEG)
      by (unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in Hin; lia).
    destruct (Z.eq_dec a (S3 + 20)) as [E|Hne].
    - subst a. exact (tf_ba_rd mm (S3 + 20) [Z_to_bv 8 1] (S3 + 20) B20 ltac:(cbn [length]; lia)).
    - exists b. unfold mrd in Hb |- *. rewrite (MU2 (wa a)); [exact Hb|].
      rewrite wa_unsigned by lia. unfold f25_W. cbn [outside].
      split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (AC2 : asan_cells mm).
  { apply (asan_cells_kept (f25_W S3 D sp) m mm HAC MU2).
    unfold f25_W. cbn [disjoint_from]. unfold RT_LO, RT_HI in *. repeat split; lia. }
  (* the byte D is addressable: its shadow byte S3 + 20 is 1 *)
  assert (ADD2 : addressable mm D 1).
  { apply (tf_addr_sh mm D 1); [lia | lia | lia | exact HD8 | intros t Ht; replace (D + t) with D by lia; exact HappD |].
    intros t Ht. replace t with 0 by lia. exists 1. change (0 / 8) with 0. rewrite Z.add_0_r, HshD.
    split; [exact B20|]. split; [lia | right; vm_compute; reflexivity]. }
  (* the ports bytes stay addressable: their shadow bytes are not S3 + 20, and D is not a shadow byte *)
  assert (ADP2 : addressable mm p 20).
  { apply (tf_addr_munch (f25_W S3 D sp) m mm p 20 Hadp MU2).
    intros i Hi. pose proof Hadp as (_ & _ & _ & Hab). destruct (Hab i Hi) as (Hap & _).
    pose proof (shadow_of_app (p + i) Hap) as Hsi.
    assert (Hsb : LOWMEM_END <= shadow_addr (p + i) < HIGHMEM_BEG)
      by (unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in Hsi; lia).
    pose proof (Hshp i Hi) as Hne.
    unfold f25_W. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  (* the runtime cells and the shadow map are outside the callee's write set *)
  assert (HPW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            outside (PUC.reac_ports_unknown_W sp D) x).
  { intros x Hx. rewrite f25_PUW by lia. cbn [outside].
    assert (HGC : GOT_CELL_K + 8 <= HIGHMEM_BEG /\ CELL_K + 8 <= HIGHMEM_BEG) by (unfold GOT_CELL_K, CELL_K; lia).
    destruct Hx as [Hx|[Hx|Hx]].
    - split; [lia|]. split; [lia | exact I].
    - split; [lia|]. split; [lia | exact I].
    - assert (Hsb : LOWMEM_END <= x < HIGHMEM_BEG)
        by (unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in Hx; lia).
      split; [lia|]. split; [lia | exact I]. }
  (* the call: the callee contract at 0x88628, back at 0x828a4 *)
  eapply evt_cut.
  { pose proof HPU as HC.
    unfold PUC.reac_ports_unknown_contract, PUC.REAC_PORTS_UNKNOWN_FRAME, PUC.REAC_PORTS_UNKNOWN in HC.
    eapply HC with (p := p) (c := D) (lo := lo) (bs := bs).
    - apply unsigned_lit. lia.
    - apply unsigned_lit. lia.
    - rewrite Hsp. exact ST2.
    - rewrite Hsp. lia.
    - intros _. rewrite Hsp. split; [lia|]. split; [exact Hlen|]. split; [exact BS2 | exact HdjpW].
    - intros _. rewrite Hsp. split; [exact WRD2|]. split; [intros _; exact HdjDp | exact HdjDW].
    - exact AC2.
    - exact SW2.
    - intros _. exact ADD2.
    - intros _. exact ADP2.
    - rewrite Hsp. exact HPW. }
  intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & m' & Ems & MU' & WM' & ST' & _ & HFB).
  subst ms'. apply evt_done. cbv beta.
  rewrite Hsp in MU', ST'. rewrite f25_PUW in MU' by lia.
  do 3 eexists. split; [reflexivity|].
  split; [apply bv_eq; vm_compute; reflexivity|].
  do 15 (split; [first [reflexivity | simp_regs; reflexivity]|]).
  split.
  { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [apply f25_sub | exact MU']. }
  split; [eapply wmono_trans; [exact WM2 | exact WM']|].
  split; [exact ST'|].
  split.
  { unfold b8 in *. eapply fl_bytes; [exact B20 | exact MU' |].
    intros x Hx. cbn [length] in Hx. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  exact (HFB ltac:(lia)).
Qed.

(* F25: the one lazy-model run of this segment is Tac_slot.sl_run_lib (AsanLift.evt_SR_canon_lazy) over f25_evt.
   Reads: the spill [A + 136, A + 144) (A = s1), and in the callee the ports bytes [phi + 18, phi + 38), their
   shadow bytes, the shadow byte S(fr) + 20 of the byte fr + 160 and the runtime cells CELL_K / GOT_CELL_K.
   Writes: the shadow byte [S(fr) + 20, S(fr) + 21), the frame byte [fr + 160, fr + 161) (by 0x82898 and again by
   the callee) and the callee's 16 stack bytes [sp - 16, sp). *)
Lemma seg_F25 : forall j : nat, Hat B APIf ra (Inv_B828a4_at B APIf ra) j -> Hat B APIf ra (Inv_B82888_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  unfold Inv_B82888_at, FCUTP in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & H18c & H20c & HFTURN &
    HLKc & HFTL & HIFS & HK & Ha0 & Hs4 & Hs7 & HS184 & Hs6 & HPO & HGAP & Hdjphi & Hs5). subst c.
  unfold F23GAP in HGAP. destruct HGAP as (Hphib & Hg50).
  (* at 50 <= flen (F27K) the cut's live block is (phi, flen) *)
  pose proof HK as (_ & _ & _ & _ & _ & Hflen0 & _).
  rewrite (tf_asize (flen g j) Hflen0) in HFRA, HENT.
  rewrite SEGS.
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & HW0).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (HfrK & _ & _ & _).
  destruct (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Hfrapp).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5f & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md HAH) as Hstkhi.
  assert (HHM : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HLM : LOWMEM_END = 2147450880) by reflexivity.
  assert (HAEv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (Esp : bv_unsigned (getr regs 2) = sp) by (unfold AC.aspZ in Haspz; exact Haspz).
  pose proof (HfrK 16 ltac:(lia)) as Hdjfr. rewrite Haspz in Hdjfr.
  rewrite Haspz in Hlow, HW0, Hdjphi.
  pose proof HK as (HLK & H18 & H27 & Hphi0 & Hphi50 & Hflen & Hblk & HS312 & HS272 & Hs8 & HS104 & HS136).
  destruct (Tac_ro.fli_mem _ _ _ _ (proj2 (proj2 (proj2 HLK)))) as (Had2624 & Hstkfr & HRid & HRfg & HKNT & Hfst).
  assert (HAE : 0 <= A < APPMEM_END) by lia.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear -Hfrm; Z.div_mod_to_equations; lia).
  assert (HappD : app_mem (fr + 160)) by (apply Hfrapp; lia).
  (* the shadow byte of the granule [fr + 160, fr + 168) is S(fr) + 20, one of the frame's 392 *)
  assert (HshD : shadow_addr (fr + 160) = Sfr fr + 20)
    by (rewrite (tf_sh_idx fr 160 Hfr8 ltac:(lia)); reflexivity).
  assert (HS20in : in_shadow (Sfr fr + 20)) by (rewrite <- HshD; apply shadow_of_app; exact HappD).
  assert (HS20b : LOWMEM_END <= Sfr fr + 20 < HIGHMEM_BEG).
  { pose proof HS20in as H. unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in H. lia. }
  (* the live block Phi is apart from the frame, app memory below stklo <= sp - FN_STACK *)
  pose proof (tf_order B APIf ra g fr phi (flen g j) regs mem md HFRA Hflen) as Hord.
  assert (HoutBlkF : forall x, phi <= x < phi + flen g j ->
            app_mem x /\ x < sp - FN_STACK /\ ~ (fr <= x < fr + FRAME_BYTES)).
  { intros x Hx. destruct (tf_blk_out B APIf ra g fr phi (flen g j) regs mem md HFRA x Hx) as (Hap & Hlo & Hnf).
    split; [exact Hap|]. split; [lia | exact Hnf]. }
  assert (Hpbs : bytes_at rsegs mem (phi + 18) (t_pbs (g_in g) j))
    by (rewrite tf_pbs; apply tf_bytes_firstn; exact Hblk).
  destruct HHB as (Hphinz & Hphiad).
  assert (Hasz : AC.a_size (flen g j) = flen g j) by (apply tf_asize; exact Hflen).
  assert (Hadp : addressable mem (phi + 18) 20)
    by (apply (addressable_sub mem phi (AC.a_size (flen g j)) 18 20 Hphiad); lia).
  assert (HshNot : forall x, 0 <= x -> ~ (fr <= x < fr + FRAME_BYTES) -> shadow_addr x <> Sfr fr + 20).
  { intros x Hx0 Hx E. apply Hx. apply (tf_sh_back fr x Hfr8 Hfr0 Hx0). lia. }
  destruct (HoutBlkF (phi + 18) ltac:(lia)) as (Ha18 & _ & _).
  destruct (HoutBlkF (phi + 37) ltac:(lia)) as (Ha37 & _ & _).
  unfold app_mem in Ha18, Ha37.
  assert (Hq136 : bytes_at rsegs mem (A + 136) (le8 (Z_to_bv 64 (fr + 160)))).
  { pose proof (tf_spill_q regs mem A 136 (fr + 160) Hr9 HAE ltac:(lia) HS136) as Hq. unfold q64 in Hq. exact Hq. }
  assert (HWR20 : wr_at rsegs mem (Sfr fr + 20) 1).
  { split; [lia|]. split; [lia|]. intros i Hi.
    replace (Sfr fr + 20 + i) with (Sfr fr + 20) by lia.
    exact (proj1 (AsanRTInv.RT_shadow_rw sp mem md HRT (Sfr fr + 20) HS20in)). }
  assert (HWRD : wr_at rsegs mem (fr + 160) 1)
    by (apply (tf_wr_of_stk mem fr (fr + FRAME_BYTES) (fr + 160) 1 Hstkfr); lia).
  set (W := f25_W (Sfr fr) (fr + 160) sp).
  apply (sl_run_lib regs (Z_to_bv 64 0x82888) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x828a4 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\
       getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 10 /\ getr R0 26 = getr regs 26 /\
       getr R0 27 = getr regs 27 /\ getr R0 10 = Z_to_bv 64 (t_unk (g_in g) j) /\
       munch W mem mem' /\ wmono rsegs mem mem' /\ stk rsegs mem' (sp - FN_STACK) sp /\
       b8 mem' (Sfr fr + 20) 1 /\ FIRSTb g fr j mem')
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f25_evt with (m := mem) (S3 := Sfr fr) (A := A) (D := fr + 160) (p := phi + 18) (sp := sp)
        (lo := sp - FN_STACK) (bs := t_pbs (g_in g) j).
      - unfold rg in Hr19. exact Hr19.
      - unfold rg in Hr9. exact Hr9.
      - unfold rg in Hs6. exact Hs6.
      - unfold rg in Hs7. exact Hs7.
      - exact Esp.
      - exact HS20b.
      - exact HshD.
      - clear -Hfr8. Z.div_mod_to_equations. lia.
      - exact HappD.
      - lia.
      - exact HWR20.
      - exact HWRD.
      - lia.
      - lia.
      - lia.
      - exact Hq136.
      - lia.
      - lia.
      - apply tf_pbs_len.
      - exact Hpbs.
      - exact Hadp.
      - intros i Hi. apply HshNot; lia.
      - lia.
      - lia.
      - exact HW0.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact (AsanRTInv.RT_cells sp mem md HRT).
      - exact (AsanRTInv.RT_shadow_rw sp mem md HRT).
      - unfold RT_HI. lia.
      - unfold GOT_CELL_K. lia.
      - unfold CELL_K. lia. }
    { intros ms' (R & pc' & m' & E & Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E24 & E25 &
                  E26 & E27 & E10 & MU & WM & ST & B20 & HF).
      exists R, pc', m'. split; [exact E|].
      split; [exact Hpc|].
      split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E8|]. split; [exact E9|].
      split; [exact E18|]. split; [exact E19|]. split; [exact E20|]. split; [exact E21|]. split; [exact E22|].
      split; [exact E24|]. split; [exact E25|]. split; [exact E26|]. split; [exact E27|].
      split; [rewrite E10, (f25_pu_ok (g_in g) j (phi + 18)) by lia; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact B20|].
      unfold FIRSTb, b8. rewrite <- (f25_pu_first (g_in g) j (phi + 18)) by lia. exact HF. }
  - (* continuation: rebuild the exit cut Inv_B828a4_at and apply it *)
    intros R0 pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 & Er24 & Er25 & Er26 & Er27 & Er10 &
       MU & WM & ST' & B20 & HFI) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 10) by (rewrite Hreg; exact Er25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (t_unk (g_in g) j)) by (rewrite Hreg; exact Er10).
    (* the addresses W misses *)
    assert (HoutSh : forall y, in_shadow y -> y <> Sfr fr + 20 -> outside W y).
    { intros y Hy Hne. assert (Hyb : LOWMEM_END <= y < HIGHMEM_BEG)
        by (unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in Hy; lia).
      pose proof HappD as HDr. unfold app_mem in HDr.
      subst W. unfold f25_W. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (HoutApp : forall y, app_mem y -> y <> fr + 160 -> (y < sp - 16 \/ sp <= y) -> outside W y).
    { intros y Hy Hne Hyy. unfold app_mem in Hy.
      subst W. unfold f25_W. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (HoutBlk : forall x, phi <= x < phi + flen g j -> outside W x).
    { intros x Hx. destruct (HoutBlkF x Hx) as (Hap & Hlo & Hnf). apply HoutApp; [exact Hap | lia | left; lia]. }
    assert (HoutA : forall y, A <= y < A + 448 -> outside W y).
    { intros y Hy. apply HoutApp; [unfold app_mem; right; lia | lia | right; lia]. }
    assert (HoutFr : forall x, fr <= x < fr + FRAME_BYTES -> x <> fr + 160 -> outside W x).
    { intros x Hx Hne. apply HoutApp; [apply Hfrapp; exact Hx | exact Hne | lia]. }
    (* the post memory is readable at every written address *)
    assert (HRDW : forall q, ~ outside W q -> exists b, mrd rsegs mem' (wa q) = Some b).
    { intros q Hq. destruct (f25_inW (Sfr fr) (fr + 160) sp q Hq) as [Hq1|[Hq2|Hq3]].
      - exact (tf_ba_rd mem' (Sfr fr + 20) [Z_to_bv 8 1] q B20 ltac:(cbn [length]; lia)).
      - exact (tf_ba_rd mem' (fr + 160) [Z_to_bv 8 (t_first (g_in g) j)] q HFI ltac:(cbn [length]; lia)).
      - pose proof ST' as (_ & _ & Hst). destruct (Hst q ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
    (* every written address is a frame shadow byte, a frame body byte or a callee window byte *)
    assert (HCL : forall q, ~ outside W q ->
              (fr + 24 <= q < fr + FRAME_BYTES) \/ (Sfr fr <= q < Sfr fr + FRAME_SHADOW) \/
              (AC.aspZ regs - FN_STACK <= q < AC.aspZ regs) \/
              (bv_unsigned (getr regs 9) + 72 <= q < bv_unsigned (getr regs 9) + 336)).
    { intros q Hq. rewrite Haspz. destruct (f25_inW (Sfr fr) (fr + 160) sp q Hq) as [Hq1|[Hq2|Hq3]].
      - right; left; lia.
      - left; lia.
      - right; right; left; lia. }
    assert (Hrtdj : rt_disjoint W) by (subst W; unfold f25_W; apply tf_rt_dj3; lia).
    assert (HGTW : forall lo hi, In (lo, hi) W -> AC.GT <= lo).
    { intros lo hi Hin. subst W. unfold f25_W in Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia. }
    assert (HroM : ro_agree rsegs mem') by exact (tf_ro_keep W mem mem' HGTW MU Hro).
    (* FRA and ENT across W (tf_fra_ent), then to regs' and md' *)
    destruct (tf_fra_ent B APIf ra empty FF g fr (hb1 phi (flen g j)) regs mem mem' md W
                HFRA HENT MU WM Hrtdj HroM HCL HRDW) as (HFRA1 & HENT1).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr _ regs regs' mem' md md' HFRA1); assumption).
    (* every spill of the save area is kept: W misses [A, A + 448) and the run keeps s1 *)
    assert (Hspk : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs mem' off v).
    { intros off v Hoff Hs. apply (tf_spill_keep regs regs mem mem' W A off v Hr9 eq_refl HAE ltac:(lia) Hs MU).
      intros x Hx. apply HoutA. lia. }
    assert (Hspk' : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hs. exact (Tac_ro.spill_reg9 regs regs' mem' off v Fr9 (Hspk off v Hoff Hs)). }
    (* the frame's shadow S(fr) >= GT / 8 + K lies above the kind-name table's shadow bytes *)
    assert (HSfr : 0x800b7c00 <= Sfr fr)
      by (clear - HGT; unfold Sfr, shadow_addr, ASAN_K; unfold AC.GT in HGT; Z.div_mod_to_equations; lia).
    (* `first` [fr + 2880, fr + 2920) stays addressable: its shadow bytes S(fr) + 360 .. 364 are not S(fr) + 20 *)
    assert (Hfst' : addressable mem' (fr + 2880) 40).
    { apply (tf_addr_munch W mem mem' (fr + 2880) 40 Hfst MU). intros i Hi.
      apply HoutSh;
        [ apply shadow_of_app; apply Hfrapp; lia
        | pose proof (tf_sh_ge fr (fr + 2880 + i) 360 Hfr8 Hfr0 ltac:(lia)) as Hge; lia ]. }
    (* F27K on the post memory (same registers), then moved to regs' by tf_K (s1, s2, s8, s11 kept) *)
    assert (HK' : F27K g j phi fr regs mem').
    { unfold F27K.
      split.
      { apply (Tac_ro.lk_keep g fr j regs regs mem mem' HLK H27).
        - apply (tf_addr_munch W mem mem' (fr + 2624) 6 Had2624 MU). intros i Hi.
          apply HoutSh.
          + apply shadow_of_app. apply Hfrapp. lia.
          + pose proof (tf_sh_ge fr (fr + 2624 + i) 328 Hfr8 Hfr0 ltac:(lia)) as Hge. lia.
        - apply (tf_stk_keep W mem mem' fr (fr + FRAME_BYTES) Hstkfr MU WM). intros x _ Ho. exact (HRDW x Ho).
        - apply (tf_addr_munch W mem mem' (fr + 2688) 38 HRid MU). intros i Hi.
          apply HoutSh;
            [ apply shadow_of_app; apply Hfrapp; lia
            | pose proof (tf_sh_ge fr (fr + 2688 + i) 336 Hfr8 Hfr0 ltac:(lia)) as Hge; lia ].
        - apply (tf_addr_munch W mem mem' (fragb fr) 72 HRfg MU). intros i Hi.
          apply HoutSh;
            [ apply shadow_of_app; apply Hfrapp; unfold fragb in *; lia
            | pose proof (tf_sh_ge fr (fragb fr + i) 346 Hfr8 Hfr0 ltac:(unfold fragb in *; lia)) as Hge;
              unfold fragb in *; lia ].
        - (* KNT: the kind-name table is image data below GT, its shadow bytes lie below S(fr) *)
          apply (tf_knt_munch W mem mem' HKNT MU).
          + intros x Hx. apply (tf_out_GT W x HGTW). unfold KNC.KIND_NAME in Hx. lia.
          + intros x Hx. apply HoutSh; [unfold in_shadow, LOWSHADOW_END; lia | lia].
        - exact Hfst'.
        - unfold OURb in *. eapply fl_bytes; [exact (proj1 (proj2 (proj2 HLK))) | exact MU |].
          rewrite OUR_length. intros x Hx. change (Z.of_nat 6) with 6 in Hx. apply HoutFr; lia.
        - exact Hspk. }
      split; [exact H18|]. split; [exact H27|]. split; [exact Hphi0|]. split; [exact Hphi50|].
      split; [exact Hflen|].
      split.
      { eapply fl_bytes; [exact Hblk | exact MU |]. rewrite tf_blk_len. intros x Hx. apply HoutBlk.
        change (Z.of_nat 32) with 32 in Hx. lia. }
      split; [exact (Hspk 312 _ ltac:(lia) HS312)|].
      split; [exact (Hspk 272 _ ltac:(lia) HS272)|].
      split; [exact Hs8|].
      split; [exact (Hspk 104 _ ltac:(lia) HS104)|].
      exact (Hspk 136 _ ltac:(lia) HS136). }
    assert (HPO' : PORTS g fr j mem').
    { apply (f25_ports_keep g fr j mem mem' W HPO MU). intros x Hx. apply HoutFr; lia. }
    assert (Easp : AC.aspZ regs' = sp) by (unfold AC.aspZ; rewrite Fr2; exact Esp).
    rewrite <- SEGS. apply Hexit.
    unfold Inv_B828a4_at.
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    rewrite Hasz.
    split; [exact HFRA'|].
    split; [eapply ent_mat; [exact HENT1 | exact Hmat]|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { split; [exact Hphinz|]. apply (tf_addr_munch W mem mem' phi _ Hphiad MU).
      intros i Hi. rewrite Hasz in Hi. destruct (HoutBlkF (phi + i) ltac:(lia)) as (Hap & _ & Hnf).
      apply HoutSh; [apply shadow_of_app; exact Hap|].
      apply HshNot; [unfold app_mem in Hap; lia | exact Hnf]. }
    split; [exact (tf_K g j phi fr regs regs' mem' HK' Fr9 Fr18 Fr24 Fr27)|].
    split; [unfold rg in Hs4 |- *; rewrite Fr20; exact Hs4|].
    split.
    { (* FTL: s5 = fr + 128 and s8 = the sum flag (kept by the run and the call), the spills [A + 184] /
         [A + 272] / [A + 312] *)
      destruct HFTL as (L21 & L184 & L272 & L24 & L312).
      split; [unfold rg in L21 |- *; rewrite Fr21; exact L21|].
      split; [exact (Hspk' 184 _ ltac:(lia) L184)|].
      split; [exact (Hspk' 272 _ ltac:(lia) L272)|].
      split; [unfold rg in L24 |- *; rewrite Fr24; exact L24 | exact (Hspk' 312 _ ltac:(lia) L312)]. }
    split; [unfold rg in Ha0 |- *; rewrite Fr25; exact Ha0|].
    split; [unfold rg; exact Fr10|].
    split; [unfold rg in Hs6 |- *; rewrite Fr22; exact Hs6|].
    split; [exact HPO'|].
    split; [exact HFI|].
    split; [rewrite Easp; exact Hdjphi|].
    split.
    { (* FTURN: the spills [A + 224] / [A + 232] and the frame bytes at Phi, inside the live block *)
      apply (Tac_ro.turn_munch g j phi regs regs' W mem mem' HFTURN Hspk' MU).
      intros x Hx. apply HoutBlk. unfold flen. lia. }
    (* s5 = fr + 128: kept by the run and the call *)
    split; [|unfold rg in Hs5 |- *; rewrite Fr21; exact Hs5].
    (* IFS (S j): the first-fragment local `first` [fr + 2880, fr + 2920) and the two frame records at
       fr + 2688 / fr + 2768, which the byte fr + 160, its shadow byte and the callee window miss *)
    apply (Tac_ro.ifs_keep g fr (S j) regs regs' mem mem' HIFS).
    + intros Hb. apply (fl_bytes W mem mem' (fr + 2688) _ Hb MU). rewrite Tac_ro.tr_ID_length.
      intros x Hx. apply HoutFr; lia.
    + intros Hb. apply (fl_bytes W mem mem' (fr + 2768) _ Hb MU). rewrite Tac_ro.tr_FG_length.
      intros x Hx. apply HoutFr; lia.
    + intros a bs Ha Hl Hb. apply (fl_bytes W mem mem' a bs Hb MU). intros x Hx. apply HoutFr; lia.
    + exact Hfst'.
Qed.

End S.
