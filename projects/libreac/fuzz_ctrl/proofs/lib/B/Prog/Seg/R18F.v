(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 537 of its 580 lines of code are new or changed and 968 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R18.v; 142 of its 225 lines of code are new or changed and 497 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R18.v r18_evt at a working branch 3803efccea0
     (blob a914935f524cf8738542f2ae660bd883ab2b63d9);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r18_evt calls declaration_of, so it is split at the call (parent a Theorem Labs lane, binding): r18_pre_F
     re-runs R18.v:167-203 (0x819d0 up to the declaration_of entry 0x83114, ra = 0x81a50) and there is no post
     stretch, because the run's exit cut Inv_B81a50_at IS the return pc (R18.v:204-246 is the contract
     application on the normalized memory alone). No `_F` steps through a callee and this file states no callee
     contract. *)
(* rule 24: no function proved. *)
(* Route (C) (a Theorem Labs lane 09:38Z, amendment 10:34Z; writer of record a Theorem Labs lane): r18_pre_F_on is r18_pre_F with the
   shadow requirement DROPPED from the continuation and the post's `shadow_rw m1` replaced by the transport
   `forall P, shadow_rw_on P m -> shadow_rw_on P m1`.  r18_pre_F has no `shadow_rw m` premise of its own; its one shadow
   requirement is the conjunct `shadow_rw m1` of R18.r18_pre (R18.v:108), which the continuation premise supplies for the
   memory after the four stores and the post only carries on.  Measured from the stretch's proof: the two shadow loads
   (0x819f0 lb at Z.shiftr (mr + 16) 3 + ASAN_K, 0x81a18 lb at Z.shiftr (mr + 20) 3 + ASAN_K) read through the
   ov_read_bytes premises (rng ... 1 each); the four shadow stores 0x81a34 .. 0x81a40 into [S + 320, S + 324)
   (S = bv_unsigned s3v) go through the rw_cells premise (rng (S + 320) 4); the two loads 0x81a44 / 0x81a48 read
   through r18_pre's ov_read_bytes conjuncts.  So the stretch reads and stores no shadow byte through `shadow_rw m1`:
   it was there only for the call (declaration_of_contract, premise `shadow_rw m`, applied by R18.v:220 at the
   normalized m1).  r18_pre_on is R18.r18_pre without that conjunct.  The call's region is the consumer's: under
   a Theorem Labs lane's coming B declaration_of_contract_on, a caller holding that contract's region at m carries it to m1 by
   the post's last conjunct at P := that region, and to the normalized m1 by B.ShadowRwOnT.shadow_rw_on_normalize (the
   post's MN.ro_agree rsegs m1).  The written bytes [S + 320, S + 324) are present in m1 (the post's bytes_at), so
   the transport holds for every region P.  r18_pre_F keeps its statement, as a corollary (the continuation through
   r18_pre_on_of_pre; the post's R18.r18_pre m1 from the old continuation at the post's m1). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcDecl RcLeaf RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import declaration_of_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp RtmB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_bp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn.
(* Last: StepF's step / if_true (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF ExecF_all StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.

(* The store hook of R18.v (`sb zero,k(s3)`: le1 v is [Z_to_bv 8 (bv_unsigned v)] by conversion), on the
   four-argument evtF goal pattern; StepF's norm_lit_store_bytes knows only the literal stores
   (pilot fix (2) (RECIPE.md (a working note, not in this delivery))). *)
Local Ltac fix_lit_storeF :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) => change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::=
  fix_lit_storeF; norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* R18.v's r18_shfix, on evtF goals. *)
Local Ltac r18F_shfix :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (MState.unsigned_lit x) by lia
  end.

(* ---- route (C): the continuation's requirement without shadow_rw, and the shadow_rw_on transport ---- *)

(* R18.r18_pre (R18.v:102-108) without its conjunct `shadow_rw m1`. *)
Definition r18_pre_on (m1 : word -> option byte) (A spv lo mr D : Z) (row : list byte) : Prop :=
  ov_read_bytes rsegs m1 (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 mr)) /\
  ov_read_bytes rsegs m1 (wa (A + 96)) 8 = Some (le8 (Z_to_bv 64 D)) /\
  stk rsegs m1 lo spv /\
  bytes_at rsegs m1 mr row /\
  (exists ob, rw_cells rsegs m1 D [CB 32 ob]) /\
  asan_cells m1 /\ addressable m1 mr 296 /\ addressable m1 D 32.

Lemma r18_pre_on_of_pre : forall m1 A spv lo mr D row,
  R18.r18_pre m1 A spv lo mr D row -> r18_pre_on m1 A spv lo mr D row.
Proof.
  intros m1 A spv lo mr D row (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8 & H9).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H8 H9))))))).
Qed.

(* Tac_bp.bp_shadow_rw under a region guard P: a munch whose written shadow bytes are present after it keeps every
   shadow_rw_on region. *)
Lemma r18_srw_on_munch : forall (P : Z -> Prop) W m m', B.ShadowRwOn.shadow_rw_on P m -> munch W m m' ->
  wmono rsegs m m' -> (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) ->
  B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P W m m' HS MU WM H a Hp Ha. destruct (HS a Hp Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* ---- the footprint form of [0x819d0, the declaration_of entry), route (C) ---- *)

Lemma r18_pre_F_on :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A D mr q v1 v2 lo : Z) (row junk : list byte),
    s1v = Z_to_bv 64 A -> s10v = Z_to_bv 64 ASAN_K -> a0v = Z_to_bv 64 0 ->
    0 <= A -> A + 448 <= 2 ^ 64 ->
    HIGHMEM_BEG <= lo -> lo + DECLARATION_OF_K <= bv_unsigned sp -> bv_unsigned sp <= APPMEM_END ->
    0 <= mr -> mr + 296 <= AC.GT -> mr mod 8 = 0 ->
    AC.GT <= bv_unsigned s3v -> bv_unsigned s3v + 324 <= HIGHMEM_BEG ->
    0 <= q -> q + 8 <= 2 ^ 64 ->
    AC.GT <= D -> D + 32 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (A + 32)) 8 = Some (le8 (Z_to_bv 64 0)) ->
    ov_read_bytes rsegs m (wa (A + 24)) 8 = Some (le8 (Z_to_bv 64 (mr + 16))) ->
    ov_read_bytes rsegs m (wa (A + 16)) 8 = Some (le8 (Z_to_bv 64 (mr + 20))) ->
    ov_read_bytes rsegs m (wa (A + 120)) 8 = Some (le8 (Z_to_bv 64 q)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 16) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 20) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa q) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (q + 4)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    ov_read_bytes rsegs m (wa (mr + 16)) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (mr + 20)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    rw_cells rsegs m (bv_unsigned s3v + 320) [CB 4 junk] ->
    MN.ro_agree rsegs m ->
    (forall m1, munch [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] m m1 -> wmono rsegs m m1 ->
       bytes_at rsegs m1 (bv_unsigned s3v + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
       r18_pre_on m1 A (bv_unsigned sp) lo mr D row) ->
    rng RNG (A + 16) 8 -> rng RNG (A + 24) 8 -> rng RNG (A + 32) 8 ->
    rng RNG (A + 96) 8 -> rng RNG (A + 120) 8 -> rng RNG (A + 272) 8 ->
    rng RNG (Z.shiftr (mr + 16) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 20) 3 + ASAN_K) 1 ->
    rng RNG (mr + 16) 4 -> rng RNG (mr + 20) 4 ->
    rng RNG q 4 -> rng RNG (q + 4) 4 ->
    rng RNG (bv_unsigned s3v + 320) 4 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 DECLARATION_OF) fc None m1 (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81a50 /\ getr R 10 = Z_to_bv 64 mr /\ getr R 11 = Z_to_bv 64 D /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1v /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
         getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10v /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] m m1 /\ wmono rsegs m m1 /\
         bytes_at rsegs m1 (bv_unsigned s3v + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] /\
         MN.ro_agree rsegs m1 /\ r18_pre_on m1 A (bv_unsigned sp) lo mr D row /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x819d0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6
    Fr fc m A D mr q v1 v2 lo row junk -> -> -> HA0 HAb Hlo HlK Hsp Hmr0 Hmrb Hmr8 HSH0 HSHb Hq0 Hqb HD0 HDb
    R32 R24 R16 R120 K16 K20 Q1 Q2 M16 M20 RWsh HRO HPRE
    Rg16 Rg24 Rg32 Rg96 Rg120 Rg272 RgK16 RgK20 RgM16 RgM20 Rgq Rgq4 Rgsh.
  unfold AC.GT in *.
  assert (Hspv : 0 <= bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  pose proof (rw_cells_bound _ _ _ _ RWsh) as HBsh. cbn [cells_size csize Nat.add] in HBsh.
  pose proof (munch_refl [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 819d0 beqz a0 (taken) *)
  step. if_true.
  (* 819d8 ld a0,32(s1) ; 819dc beqz a0 (taken; the trap 819e0 is not reached) *)
  step. step. if_true.
  (* 819e4 ld a3,24(s1) ; 819e8 srli a0,a3,3 ; 819ec add a0,a0,s10 *)
  step. step. step. r18F_shfix.
  (* 819f0 lb a1,0(a0) ; 819f4 ld a0,120(s1) ; 819f8 lw a0,0(a0) *)
  step. step. step.
  (* 819fc bnez a1 (not taken) *)
  step. first [ if_false | if_false_by R18.r18_nz0 ].
  (* 81a00 lw a1,0(a3) ; 81a04 beq a0,a1 (taken) *)
  step. step. if_true_by (R18.r18_eqb_refl (sx32 (Z_to_bv 64 v1))).
  (* 81a0c ld a3,16(s1) ; 81a10 srli ; 81a14 add *)
  step. step. step. r18F_shfix.
  (* 81a18 lb a1,0(a0) ; 81a1c ld a0,120(s1) ; 81a20 lw a0,4(a0) *)
  step. step. step.
  (* 81a24 bnez a1 (not taken) *)
  step. first [ if_false | if_false_by R18.r18_nz0 ].
  (* 81a28 lw a1,0(a3) ; 81a2c beq a0,a1 (taken) *)
  step. step. if_true_by (R18.r18_eqb_refl (sx32 (Z_to_bv 64 v2))).
  (* 81a34 .. 81a40 : the four shadow stores, into the 4-byte cell run at S(fr) + 320 *)
  step. step. step. step.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => tryif constr_eq mm m1 then idtac else rename mm into m1
  end.
  assert (B4 : bytes_at rsegs m1 (bv_unsigned s3v + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
  { lazymatch goal with
    | H : rw_cells rsegs m1 (bv_unsigned s3v + 320) ?cs |- _ =>
        destruct H as ((_ & HB) & _); eapply bytes_at_ext; [exact HB | first [reflexivity | vm_compute; reflexivity]]
    end. }
  assert (MI : MN.ro_agree rsegs m1).
  { apply (rh_ro_keep m m1 [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] HRO MU). intros x Hx.
    pose proof (rh_ro_lt x Hx) as Hlt. unfold AC.GT in Hlt. cbn [outside]. split; [lia | exact I]. }
  assert (TR : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1).
  { intros P HP. apply (r18_srw_on_munch P _ m m1 HP MU WM). intros a Ha.
    destruct (Z_le_gt_dec (bv_unsigned s3v + 320) a) as [H1|H1];
      [destruct (Z_lt_ge_dec a (bv_unsigned s3v + 324)) as [H2|H2]|].
    - right. apply (Tac_bp.bp_ba_rd m1 (bv_unsigned s3v + 320) _ a B4).
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - left. cbn [outside]. split; [lia | exact I].
    - left. cbn [outside]. split; [lia | exact I]. }
  pose proof (HPRE m1 MU WM B4) as HPR.
  destruct HPR as (R272 & R96 & STc & HROW & (ob & HOB) & HAC & HAmr & HAD).
  (* 81a44 ld a0,272(s1) ; 81a48 ld a1,96(s1) ; 81a4c jal declaration_of *)
  step. step. step.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  do 18 (split; [first [ reflexivity | f_equal; lia ]|]).
  split; [exact MU|]. split; [exact WM|]. split; [exact B4|]. split; [exact MI|].
  split; [|exact TR].
  unfold r18_pre_on.
  split; [exact R272|]. split; [exact R96|]. split; [exact STc|]. split; [exact HROW|].
  split; [exists ob; exact HOB|]. split; [exact HAC|].
  split; [exact HAmr | exact HAD].
Qed.

(* ---- the footprint form of [0x819d0, the declaration_of entry) ---- *)

Lemma r18_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A D mr q v1 v2 lo : Z) (row junk : list byte),
    s1v = Z_to_bv 64 A -> s10v = Z_to_bv 64 ASAN_K -> a0v = Z_to_bv 64 0 ->
    0 <= A -> A + 448 <= 2 ^ 64 ->
    HIGHMEM_BEG <= lo -> lo + DECLARATION_OF_K <= bv_unsigned sp -> bv_unsigned sp <= APPMEM_END ->
    0 <= mr -> mr + 296 <= AC.GT -> mr mod 8 = 0 ->
    AC.GT <= bv_unsigned s3v -> bv_unsigned s3v + 324 <= HIGHMEM_BEG ->
    0 <= q -> q + 8 <= 2 ^ 64 ->
    AC.GT <= D -> D + 32 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (A + 32)) 8 = Some (le8 (Z_to_bv 64 0)) ->
    ov_read_bytes rsegs m (wa (A + 24)) 8 = Some (le8 (Z_to_bv 64 (mr + 16))) ->
    ov_read_bytes rsegs m (wa (A + 16)) 8 = Some (le8 (Z_to_bv 64 (mr + 20))) ->
    ov_read_bytes rsegs m (wa (A + 120)) 8 = Some (le8 (Z_to_bv 64 q)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 16) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 20) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa q) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (q + 4)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    ov_read_bytes rsegs m (wa (mr + 16)) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (mr + 20)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    rw_cells rsegs m (bv_unsigned s3v + 320) [CB 4 junk] ->
    MN.ro_agree rsegs m ->
    (forall m1, munch [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] m m1 -> wmono rsegs m m1 ->
       bytes_at rsegs m1 (bv_unsigned s3v + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
       R18.r18_pre m1 A (bv_unsigned sp) lo mr D row) ->
    rng RNG (A + 16) 8 -> rng RNG (A + 24) 8 -> rng RNG (A + 32) 8 ->
    rng RNG (A + 96) 8 -> rng RNG (A + 120) 8 -> rng RNG (A + 272) 8 ->
    rng RNG (Z.shiftr (mr + 16) 3 + ASAN_K) 1 -> rng RNG (Z.shiftr (mr + 20) 3 + ASAN_K) 1 ->
    rng RNG (mr + 16) 4 -> rng RNG (mr + 20) 4 ->
    rng RNG q 4 -> rng RNG (q + 4) 4 ->
    rng RNG (bv_unsigned s3v + 320) 4 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 DECLARATION_OF) fc None m1 (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81a50 /\ getr R 10 = Z_to_bv 64 mr /\ getr R 11 = Z_to_bv 64 D /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1v /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
         getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10v /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3v + 320, bv_unsigned s3v + 324)] m m1 /\ wmono rsegs m m1 /\
         bytes_at rsegs m1 (bv_unsigned s3v + 320) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] /\
         MN.ro_agree rsegs m1 /\ R18.r18_pre m1 A (bv_unsigned sp) lo mr D row)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x819d0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11 t3 t4 t5 t6
    Fr fc m A D mr q v1 v2 lo row junk Hs1 Hs10 Ha0 HA0 HAb Hlo HlK Hsp Hmr0 Hmrb Hmr8 HSH0 HSHb Hq0 Hqb HD0 HDb
    R32 R24 R16 R120 K16 K20 Q1 Q2 M16 M20 RWsh HRO HPRE
    Rg16 Rg24 Rg32 Rg96 Rg120 Rg272 RgK16 RgK20 RgM16 RgM20 Rgq Rgq4 Rgsh.
  refine (evtF_mono rsegs RNG _ _ _
            (r18_pre_F_on RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10v s11
               t3 t4 t5 t6 Fr fc m A D mr q v1 v2 lo row junk Hs1 Hs10 Ha0 HA0 HAb Hlo HlK Hsp Hmr0 Hmrb Hmr8 HSH0 HSHb
               Hq0 Hqb HD0 HDb R32 R24 R16 R120 K16 K20 Q1 Q2 M16 M20 RWsh HRO
               (fun m1 MU WM B4 => r18_pre_on_of_pre m1 A (bv_unsigned sp) lo mr D row (HPRE m1 MU WM B4))
               Rg16 Rg24 Rg32 Rg96 Rg120 Rg272 RgK16 RgK20 RgM16 RgM20 Rgq Rgq4 Rgsh) _).
  intros ms' (R & m1 & E & G1 & G10 & G11 & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 &
              G25 & G26 & G27 & MU & WM & B4 & MI & _ & _).
  exists R, m1.
  exact (conj E (conj G1 (conj G10 (conj G11 (conj G2 (conj G3 (conj G4 (conj G8 (conj G9 (conj G18 (conj G19
           (conj G20 (conj G21 (conj G22 (conj G23 (conj G24 (conj G25 (conj G26 (conj G27
           (conj MU (conj WM (conj B4 (conj MI (HPRE m1 MU WM B4)))))))))))))))))))))))).
Qed.
