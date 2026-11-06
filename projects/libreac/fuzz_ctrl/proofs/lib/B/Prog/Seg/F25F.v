(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2065 of its 2181 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3.v, with its module paths, module names, addresses and numbers changed; 415 of its 490 lines of code are new or changed and 2106 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F25.v, with its module names changed; 125 of its 216 lines of code are new or changed and 399 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/F25.v f25_evt (:125) at a working branch 3803efccea0
     (blob 1da81b404de775e28447fbfc9e953350839e7717);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f25_evt calls reac_ports_unknown (jal at 0x828a0), so it is split: f25_pre_F re-runs F25.v:159-242
     (0x82888 -> the callee entry 0x88628, ra = 0x828a4), carrying to the callee entry exactly the facts about
     the post-store memory that f25_evt feeds to the contract, and f25_post_F re-runs F25.v:259-272 (the return
     pc 0x828a4 -> the run's end, no step), with the callee post facts as premises. *)
(* Route (C) (a Theorem Labs lane 09:38Z, amendment 10:34Z; a Theorem Labs lane, 2026-10-29): f25_pre_F_on carries the proof; f25_pre_F
   keeps its statement as a corollary.  Measured from the run: its one shadow byte is the one it stores into,
   S3 + 20 (the `rng RNG (S3 + 20) 1` row; `sb s7,20(s3)` at 0x8288c), and that store's store_ok comes from
   `wr_at rsegs m (S3 + 20) 1`, not from `shadow_rw m`; the run reads no shadow byte ([A + 136, +8) and [D, +1) are
   application memory).  `shadow_rw m` only built the post `shadow_rw m'`.  So in f25_pre_F_on the premise
   `shadow_rw m` is dropped, and the post `shadow_rw m'` is `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (the
   two stores keep every present byte, B.Prog.MemMono.rd_mono, and every writable byte, wmono). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F25.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ShadowRwOnT.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module PUC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ports_unknown_c.

(* The two stores write the low byte of a register, i.e. `le1 v` with v a variable, which StepF's cell_of_bytes
   does not recognise; F25's own run rewrites it first (F25.f25_le1), so the store hook has to do the same
   (pilot fix (2)). *)
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
           lazymatch v with zxb _ => fail | _ => rewrite (F25.f25_le1 v) end
       end);
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* The pre half of f25_evt: 0x82888 mv s9,a0 ; sb s7,20(s3) ; ld a1,136(s1) ; li a0,-18 ; sb a0,0(a1) ;
   mv a0,s6 ; jal reac_ports_unknown, stopping at the callee entry 0x88628 with ra = 0x828a4.  The post carries
   exactly the facts about the written memory that f25_evt gives the callee contract. *)
Lemma f25_pre_F_on :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
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
    asan_cells m -> RT_HI <= D -> GOT_CELL_K + 8 <= D -> CELL_K + 8 <= D ->
    rng RNG (S3 + 20) 1 -> rng RNG (A + 136) 8 -> rng RNG D 1 ->
    evtF rsegs RNG
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 0x828a4) x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 A) (Z_to_bv 64 p) (Z_to_bv 64 D)
                       x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S3) x20 x21 (Z_to_bv 64 p) (Z_to_bv 64 1) x24
                       x10 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 PUC.REAC_PORTS_UNKNOWN) fc None m' (seg_rom rsegs)
         /\ munch (F25.f25_W S3 D sp) m m' /\ wmono rsegs m m' /\ stk rsegs m' lo sp
         /\ b8 m' (S3 + 20) 1 /\ wr_at rsegs m' D 1 /\ bytes_at rsegs m' p bs
         /\ (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m') /\ asan_cells m'
         /\ addressable m' D 1 /\ addressable m' p 20)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 A D p sp lo bs -> -> -> -> Hsp HS3 HshD HD8 HappD HD0 HWR20 HWRD HA0 HA1 HSA H136
    Hp0 Hp1 Hlen Hbs Hadp Hshp HdjSp HdjDp Hstk Hlo16 Hlohi HdjpW HdjDW HAC HRTD HGOT HCELL R20 R136 RD.
  assert (HLM : LOWMEM_END = 2147450880) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAEv : APPMEM_END = 140737488355328) by reflexivity.
  pose proof HappD as HDr. unfold app_mem in HDr.
  (* 0x82888 mv s9,a0 *)
  step.
  (* 0x8288c sb s7,20(s3): the shadow byte S3 + 20 becomes 1 *)
  assert (HS20 : store_ok rsegs m (wa (S3 + 20)) 1 = true).
  { pose proof (wr_at_store_ok rsegs m (S3 + 20) 1 0 1%nat HWR20 ltac:(lia) ltac:(cbn; lia)) as HH.
    rewrite Z.add_0_r in HH. exact HH. }
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
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
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => pose (mm := m2); change m2 with mm end.
  assert (MU2 : munch (F25.f25_W S3 D sp) m mm).
  { subst mm. unfold F25.f25_W.
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
                              | rewrite F25.f25_le1, unsigned_lit by lia; reflexivity ] | lia | lia ].
    - lia.
    - lia.
    - lia. }
  assert (RD2 : B.Prog.MemMono.rd_mono m mm)
    by (subst mm; repeat apply B.Prog.MemMono.rd_mono_write; apply B.Prog.MemMono.rd_mono_refl).
  assert (AC2 : asan_cells mm).
  { apply (asan_cells_kept (F25.f25_W S3 D sp) m mm HAC MU2).
    unfold F25.f25_W. cbn [disjoint_from]. unfold RT_LO, RT_HI in *. repeat split; lia. }
  assert (ADD2 : addressable mm D 1).
  { apply (tf_addr_sh mm D 1); [lia | lia | lia | exact HD8 | intros t Ht; replace (D + t) with D by lia; exact HappD |].
    intros t Ht. replace t with 0 by lia. exists 1. change (0 / 8) with 0. rewrite Z.add_0_r, HshD.
    split; [exact B20|]. split; [lia | right; vm_compute; reflexivity]. }
  assert (ADP2 : addressable mm p 20).
  { apply (tf_addr_munch (F25.f25_W S3 D sp) m mm p 20 Hadp MU2).
    intros i Hi. pose proof Hadp as (_ & _ & _ & Hab). destruct (Hab i Hi) as (Hap & _).
    pose proof (shadow_of_app (p + i) Hap) as Hsi.
    assert (Hsb : LOWMEM_END <= shadow_addr (p + i) < HIGHMEM_BEG)
      by (unfold in_shadow, LOWSHADOW_END, HIGHSHADOW_BEG in Hsi; lia).
    pose proof (Hshp i Hi) as Hne.
    unfold F25.f25_W. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  apply evtF_done.
  exists mm. split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact ST2|].
  split; [exact B20|]. split; [exact WRD2|]. split; [exact BS2|].
  split; [intros P HP; exact (B.ShadowRwOnT.shadow_rw_on_mem_mono P m mm HP WM2 RD2)|].
  split; [exact AC2|]. split; [exact ADD2 | exact ADP2].
Qed.

(* The old statement, from the narrowed one (the post at P := fun _ => True: B.ShadowRwOn.shadow_rw_on_of_shadow_rw
   and B.ShadowRwOn.shadow_rw_of_on_all). *)
Lemma f25_pre_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
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
    rng RNG (S3 + 20) 1 -> rng RNG (A + 136) 8 -> rng RNG D 1 ->
    evtF rsegs RNG
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 0x828a4) x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 A) (Z_to_bv 64 p) (Z_to_bv 64 D)
                       x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S3) x20 x21 (Z_to_bv 64 p) (Z_to_bv 64 1) x24
                       x10 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 PUC.REAC_PORTS_UNKNOWN) fc None m' (seg_rom rsegs)
         /\ munch (F25.f25_W S3 D sp) m m' /\ wmono rsegs m m' /\ stk rsegs m' lo sp
         /\ b8 m' (S3 + 20) 1 /\ wr_at rsegs m' D 1 /\ bytes_at rsegs m' p bs
         /\ shadow_rw m' /\ asan_cells m' /\ addressable m' D 1 /\ addressable m' p 20)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82888) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 A D p sp lo bs E19 E9 E22 E23 Hsp HS3 HshD HD8 HappD HD0 HWR20 HWRD HA0 HA1 HSA H136
    Hp0 Hp1 Hlen Hbs Hadp Hshp HdjSp HdjDp Hstk Hlo16 Hlohi HdjpW HdjDW HAC HSW HRTD HGOT HCELL R20 R136 RD.
  eapply evtF_mono;
    [exact (f25_pre_F_on RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
              x25 x26 x27 x28 x29 x30 x31 Fr fc m S3 A D p sp lo bs E19 E9 E22 E23 Hsp HS3 HshD HD8 HappD HD0
              HWR20 HWRD HA0 HA1 HSA H136 Hp0 Hp1 Hlen Hbs Hadp Hshp HdjSp HdjDp Hstk Hlo16 Hlohi HdjpW HdjDW HAC
              HRTD HGOT HCELL R20 R136 RD)|].
  intros ms' (m' & Ems & MU & WM & ST & B20 & WRD & BS & SW & AC & ADD & ADP).
  exists m'. do 7 (split; [assumption|]).
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m' (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)))|].
  do 2 (split; [assumption|]). exact ADP.
Qed.

(* The post half of f25_evt (F25.v:259-272): from the return pc 0x828a4 there is no further instruction before
   the run's exit cut.  The premises are the reac_ports_unknown post clauses f25_evt reads at that point, stated
   over the post-call state, plus the two facts about the pre-call memory it carries through (the segment's
   write set and the shadow byte it wrote). *)
Lemma f25_post_F :
  forall (RNG : footprint)
         (ra' x2 x3 x4 t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          t3' x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m mm m' : word -> option byte)
         (S3 D p sp lo res fb : Z) (bs : list byte),
    0 < D -> LOWMEM_END <= S3 + 20 < HIGHMEM_BEG -> HIGHMEM_BEG <= D ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    munch (F25.f25_W S3 D sp) m mm -> wmono rsegs m mm -> b8 mm (S3 + 20) 1 ->
    munch [(sp - 16, sp); (D, D + 1)] mm m' -> wmono rsegs mm m' -> stk rsegs m' lo sp ->
    bytes_at rsegs m' D [Z_to_bv 8 fb] ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (pc' : word) m'',
         ms' = MS R Fr pc' fc None m'' (seg_rom rsegs) /\ pc' = Z_to_bv 64 0x828a4 /\
         getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
         getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\ getr R 22 = x22 /\
         getr R 24 = x24 /\
         getr R 25 = x25 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
         getr R 10 = Z_to_bv 64 res /\
         munch (F25.f25_W S3 D sp) m m'' /\ wmono rsegs m m'' /\ stk rsegs m'' lo sp /\ b8 m'' (S3 + 20) 1 /\
         bytes_at rsegs m'' D [Z_to_bv 8 fb])
      (MS (mkR ra' x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7'
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' x29 x30 x31)
          Fr (Z_to_bv 64 0x828a4) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra' x2 x3 x4 t0' t1' t2' x8 x9 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    t3' x29 x30 x31 Fr fc m mm m' S3 D p sp lo res fb bs HD0 HS3 HDhi Hlohi Hlo16 MU2 WM2 B20 MU' WM' ST' HFB.
  assert (HLM : LOWMEM_END = 2147450880) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 17594333495296) by reflexivity.
  apply evtF_done. cbv beta.
  do 3 eexists. split; [reflexivity|].
  split; [reflexivity|].
  do 15 (split; [first [reflexivity | simp_regs; reflexivity]|]).
  split.
  { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [apply F25.f25_sub | exact MU']. }
  split; [eapply wmono_trans; [exact WM2 | exact WM']|].
  split; [exact ST'|].
  split.
  { unfold b8 in *. eapply fl_bytes; [exact B20 | exact MU' |].
    intros x Hx. cbn [length] in Hx. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  exact HFB.
Qed.
